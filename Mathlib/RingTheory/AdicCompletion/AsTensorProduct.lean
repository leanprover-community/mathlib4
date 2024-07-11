/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.TensorProduct.Basic

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`(AdicCompletion I R) ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show

- it is an isomorphism if `M = R^n`.
- it is surjective, if `M` is a finite `R`-module.

## TODO

- Show that `ofTensorProduct` is an isomorphism for any finite free `R`-module over an arbitrary
  ring. This is mostly composing with the isomorphism to `R^n` and checking that a diagram commutes.

-/

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

private noncomputable
def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    ext n
    simp [mul_smul (r.val n)]

@[simp]
private lemma ofTensorProductBil_apply_apply (r : AdicCompletion I R) (x : M) :
    ((AdicCompletion.ofTensorProductBil I M) r) x = r • (of I M) x :=
  rfl

/-- The natural `AdicCompletion I R`-linear map from `AdicCompletion I R ⊗[R] M` to
the adic completion of `M`. -/
noncomputable
def ofTensorProduct : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift (ofTensorProductBil I M)

@[simp]
lemma ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  simp [ofTensorProduct]

variable {M} in
/-- `ofTensorProduct` is functorial in `M`. -/
lemma ofTensorProduct_naturality (f : M →ₗ[R] N) :
    map I f ∘ₗ ofTensorProduct I M =
      ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp

section PiFintype

/-
In this section we show that `ofTensorProduct` is an isomorphism if `M = R^n`.
-/

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private lemma piEquivOfFintype_comp_ofTensorProduct_eq :
    piEquivOfFintype I (fun _ : ι ↦ R) ∘ₗ ofTensorProduct I (ι → R) =
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul, -Algebra.id.smul_eq_mul]
  split <;> simp only [smul_eq_mul, val_zero, val_one]

private lemma ofTensorProduct_eq :
    ofTensorProduct I (ι → R) = (piEquivOfFintype I (ι := ι) (fun _ : ι ↦ R)).symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι, ← LinearMap.comp_assoc]
  simp

/- If `M = R^ι` and `ι` is finite, we may construct an inverse to `ofTensorProduct I (ι → R)`. -/
private noncomputable def ofTensorProductInvOfPiFintype :
    AdicCompletion I (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (ι → R) :=
  letI f := piEquivOfFintype I (fun _ : ι ↦ R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

private lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct :
    ofTensorProductInvOfPiFintype I ι ∘ₗ ofTensorProduct I (ι → R) = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, LinearMap.comp_assoc, piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

private lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype :
    ofTensorProduct I (ι → R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, ofTensorProduct_eq, LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

/-- `ofTensorProduct` as an equiv in the case of `M = R^ι` where `ι` is finite. -/
noncomputable def ofTensorProductEquivOfPiFintype :
    AdicCompletion I R ⊗[R] (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (ι → R) :=
  LinearEquiv.ofLinear
    (ofTensorProduct I (ι → R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

/-- If `M = R^ι`, `ofTensorProduct` is bijective. -/
lemma ofTensorProduct_bijective_of_pi_of_fintype :
    Function.Bijective (ofTensorProduct I (ι → R)) :=
  EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

end PiFintype

/-- If `M` is a finite `R`-module, then the canonical map
`AdicCompletion I R ⊗[R] M →ₗ AdicCompletion I M` is surjective. -/
lemma ofTensorProduct_surjective_of_fg [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_comp, g]
    apply Function.Surjective.comp
    · exact AdicCompletion.map_surjective I hp
    · exact (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).surjective
  exact Function.Surjective.of_comp hf

end AdicCompletion
