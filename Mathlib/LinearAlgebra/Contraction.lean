/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

It also constructs linear equivalences between tensor products of hom modules and hom modules of
tensor products:
* `lTensorHomEquivHomLTensor`: `P ⊗ Hom(M, Q) ≃ₗ Hom(M, P ⊗ Q)` for `M` finite projective
* `rTensorHomEquivHomRTensor`: `Hom(M, P) ⊗ Q ≃ₗ Hom(M, P ⊗ Q)` for `M` finite projective
* `TensorProduct.homTensorHomEquiv`: `Hom(M, P) ⊗ Hom(N, Q) ≃ₗ Hom(M ⊗ N, P ⊗ Q)` for `M`, `N`
  finite projective
* `TensorProduct.dualDistribEquiv`: `Dual M ⊗ Dual N ≃ₗ Dual (M ⊗ N)` for `M`, `N` finite
  projective

## Tags

contraction, dual module, tensor product
-/

@[expose] public section

open Function LinearMap Matrix Module TensorProduct

variable {R M N P Q : Type*}

-- Enable extensionality of maps out of the tensor product.
-- High priority so it takes precedence over `LinearMap.ext`.
attribute [local ext high] TensorProduct.ext

section Contraction
section CommSemiring

variable (R M N P Q) [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

/-- The natural left-handed pairing between a module and its dual. -/
def contractLeft : Module.Dual R M ⊗[R] M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/-- The natural right-handed pairing between a module and its dual. -/
def contractRight : M ⊗[R] Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dualTensorHom : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry (.id R) M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

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

@[simp]
theorem transpose_dualTensorHom (f : Module.Dual R M) (m : M) :
    Dual.transpose (R := R) (dualTensorHom R M M (f ⊗ₜ m)) =
    dualTensorHom R _ _ (Dual.eval R M m ⊗ₜ f) := by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    map_smulₛₗ, RingHom.id_apply, smul_eq_mul, Dual.eval_apply,
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

attribute [-ext] AlgebraTensorModule.curry_injective in
theorem map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q) :
    TensorProduct.map (dualTensorHom R M P (f ⊗ₜ[R] p)) (dualTensorHom R N Q (g ⊗ₜ[R] q)) =
      dualTensorHom R (M ⊗[R] N) (P ⊗[R] Q) (dualDistrib R M N (f ⊗ₜ g) ⊗ₜ[R] (p ⊗ₜ[R] q)) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply,
    ← smul_tmul_smul]

@[simp]
theorem comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P) :
    dualTensorHom R N P (g ⊗ₜ[R] p) ∘ₗ dualTensorHom R M N (f ⊗ₜ[R] n) =
      g n • dualTensorHom R M P (f ⊗ₜ p) := by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

/-- As a matrix, `dualTensorHom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
theorem toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Finite n] [DecidableEq m]
    [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.coord j ⊗ₜ bN i)) = single i j 1 := by
  ext i' j'
  by_cases hij : i = i' ∧ j = j'
  · simp [LinearMap.toMatrix_apply, hij]
  · rw [and_iff_not_or_not, Classical.not_not] at hij
    rcases hij with hij | hij <;> simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

attribute [-ext] AlgebraTensorModule.curry_injective in
/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
-- We manually create simp-lemmas because `@[simps]` generates a malformed lemma
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinear (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

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

/-- `dualTensorHom` is natural in the source module: precomposing with `f : M' →ₗ M''`
corresponds to transposing along the dual factor. -/
theorem dualTensorHom_comp_rTensor_dualMap {M' M'' : Type*} [AddCommMonoid M'] [AddCommMonoid M'']
    [Module R M'] [Module R M''] (f : M' →ₗ[R] M'') :
    dualTensorHom R M' N ∘ₗ f.dualMap.rTensor N = f.lcomp R N ∘ₗ dualTensorHom R M'' N := by
  ext g n m
  simp [dualTensorHom_apply, LinearMap.lcomp_apply]

variable [Module.Finite R M] [Projective R M]

/-- `Hom(M, R) ⊗ N` is isomorphic to `Hom(M, N)` for finite projective `M`. -/
lemma dualTensorHom_bijective : Bijective (dualTensorHom R M N) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have hgf : (g.dualMap.rTensor N).comp (f.dualMap.rTensor N) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, LinearMap.dualMap_comp_dualMap, hfg, LinearMap.dualMap_id,
      LinearMap.rTensor_id]
  have hf : Injective (f.dualMap.rTensor N) :=
    LeftInverse.injective (g := g.dualMap.rTensor N) (DFunLike.congr_fun hgf)
  refine ⟨.of_comp (f := f.lcomp R N) ?_, fun φ ↦ ?_⟩
  · rw [← LinearMap.coe_comp, ← dualTensorHom_comp_rTensor_dualMap f, LinearMap.coe_comp]
    exact (dualTensorHomEquivOfBasis <| Pi.basisFun ..).injective.comp hf
  · obtain ⟨t, ht⟩ := (dualTensorHomEquivOfBasis <| Pi.basisFun ..).surjective (f.lcomp R N φ)
    refine ⟨g.dualMap.rTensor N t, ?_⟩
    simp only [dualTensorHomEquivOfBasis_apply] at ht
    have key := DFunLike.congr_fun (dualTensorHom_comp_rTensor_dualMap g) t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ht] at key
    rw [key, lcomp_apply', lcomp_apply', LinearMap.comp_assoc, hfg, LinearMap.comp_id]

variable (R M N) in
/-- If `M` is finite projective, the natural map $M^* ⊗ N → Hom(M, N)$ is an equivalence. -/
noncomputable def dualTensorHomEquiv : Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  .ofBijective (dualTensorHom R M N) dualTensorHom_bijective

@[simp] lemma dualTensorHomEquiv_toLinearMap :
    (dualTensorHomEquiv R M N).toLinearMap = dualTensorHom R M N := rfl

@[simp] lemma dualTensorHomEquiv_apply (f : Dual R M) (m : M) (n : N) :
    dualTensorHomEquiv R M N (f ⊗ₜ n) m = f m • n := rfl

@[simp] lemma dualTensorHomEquiv_symm_cancel_left (x : Dual R M ⊗[R] N) :
    (dualTensorHomEquiv R M N).symm (dualTensorHom R M N x) = x :=
  (dualTensorHomEquiv R M N).symm_apply_apply _

@[simp] lemma dualTensorHomEquiv_symm_cancel_right (x : M →ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquiv R M N).symm x) = x :=
  (dualTensorHomEquiv R M N).apply_symm_apply _

@[simp] lemma dualTensorHomEquivOfBasis_eq_dualTensorHomEquiv (b : Basis ι R M) :
    dualTensorHomEquivOfBasis b = dualTensorHomEquiv R M N := by
  apply LinearEquiv.toLinearMap_injective; ext; simp

end CommSemiring

end Contraction

section HomTensorHom

section CommSemiring
variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Projective R M] [Module.Finite R M] [Projective R N] [Module.Finite R N]

variable (R M P Q) in
/-- When `M` is a finite projective module, the map `lTensorHomToHomLTensor` is an equivalence. Note
that `lTensorHomEquivHomLTensor` is not defined directly in terms of
`lTensorHomToHomLTensor`, but the equivalence between the two is given by
`lTensorHomEquivHomLTensor_toLinearMap` and `lTensorHomEquivHomLTensor_apply`. -/
noncomputable def lTensorHomEquivHomLTensor : P ⊗[R] (M →ₗ[R] Q) ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

variable (R M P Q) in
/-- When `M` is a finite projective module, the map `rTensorHomToHomRTensor` is an equivalence. Note
that `rTensorHomEquivHomRTensor` is not defined directly in terms of
`rTensorHomToHomRTensor`, but the equivalence between the two is given by
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`. -/
noncomputable def rTensorHomEquivHomRTensor : (M →ₗ[R] P) ⊗[R] Q ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (dualTensorHomEquiv R M P).symm (.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
theorem lTensorHomEquivHomLTensor_toLinearMap :
    (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor (.id R) M P Q := by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp [e, lTensorHomEquivHomLTensor]

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor (.id R) M P Q := by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

@[simp]
theorem lTensorHomEquivHomLTensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap]

@[simp]
theorem rTensorHomEquivHomRTensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]

end CommSemiring

end HomTensorHom

namespace TensorProduct

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [AddCommMonoid P] [AddCommMonoid Q] [Module R P] [Module R Q]

variable [Module.Finite R M] [Module.Finite R N] [Projective R M] [Projective R N]

variable (R M N P Q) in
/-- For `M`, `N` finitely generated projective modules, `Hom (M, P) ⊗ Hom (N, Q)` is linearly
equivalent to `Hom(M ⊗ N, P ⊗ Q)` via the map `homTensorHomMap`. -/
noncomputable def homTensorHomEquiv :
    (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  -- We make sure `homTensorHomEquiv_toLinearMap` is true by definition.
  .ofBijective (homTensorHomMap (.id R) M N P Q) <| by
    convert (rTensorHomEquivHomRTensor R M P _ ≪≫ₗ (LinearEquiv.refl R M).arrowCongr
      (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ lift.equiv _ M N _).bijective
    congr
    ext
    simp

@[simp]
lemma homTensorHomEquiv_toLinearMap :
    (homTensorHomEquiv R M N P Q).toLinearMap = homTensorHomMap (.id R) M N P Q := rfl

@[simp] lemma homTensorHomEquiv_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
    homTensorHomEquiv R M N P Q (f ⊗ₜ g) (m ⊗ₜ n) = f m ⊗ₜ g n := rfl

end TensorProduct

namespace TensorProduct
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

section
variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

variable (R M N) in
/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  homTensorHomEquiv R M N R R ≪≫ₗ (TensorProduct.rid R R).congrRight

@[simp] lemma toLinearMap_dualDistribEquiv : dualDistribEquiv R M N = dualDistrib R M N := by
  ext; simp [dualDistribEquiv, mul_comm]

@[simp] lemma dualDistribEquiv_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistribEquiv R M N (f ⊗ₜ g) (m ⊗ₜ n) = g n * f m := rfl

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- An inverse to `TensorProduct.dualDistrib` given bases. -/
@[deprecated dualDistribEquiv (since := "2026-07-07")]
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[deprecated dualDistribEquiv (since := "2026-07-07")]
lemma dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]

@[deprecated dualDistribEquiv (since := "2026-07-07")]
lemma dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    (dualDistrib R M N).comp (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

@[deprecated dualDistribEquiv (since := "2026-07-07")]
lemma dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    (dualDistribInvOfBasis b c).comp (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`. -/
@[simps!, deprecated dualDistribEquiv (since := "2026-07-07")]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine .ofLinear (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

end TensorProduct
