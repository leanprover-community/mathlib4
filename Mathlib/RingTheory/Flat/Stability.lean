/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Flatness is stable under composition and base change

We show that flatness is stable under composition and base change. The latter is not formalized yet.

## Main theorems

* `Module.Flat.comp`: if `S` is a flat `R`-algebra and `M` is a flat `S`-module,
                      then `M` is a flat `R`-module

## TODO

* Show that flatness is stable under base change, i.e. if `S` is any `R`-algebra and `M` is a flat
  `R`-module, then `M ⊗[R] S` is a flat `S`-module.

-/

universe u v w

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

namespace Module.Flat

/-! ### Composition

Let `R` be a ring, `S` a flat `R`-algebra and `M` a flat `S`-module. To show that `M` is flat
as an `R`-module, we show that the inclusion of an `R`-ideal `I` into `R` tensored on the left with
`M` is injective. For this consider the composition of natural maps

`M ⊗[R] I ≃ M ⊗[S] (S ⊗[R] I) ≃ M ⊗[S] J → M ⊗[S] S → M ≃ M ⊗[R] R`

where `J` is the image of `S ⊗[R] I` under the (by flatness of `S`) injective map
`S ⊗[R] I → S`. One checks that this composition is precisely `I → R` tensored on the left
with `M` and the former is injective as a composition of injective maps (note that
`M ⊗[S] S → M` is injective because `M` is `S`-flat).
-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private noncomputable abbrev auxRightMul (I : Ideal R) : M ⊗[R] I →ₗ[S] M := by
  letI i : M ⊗[R] I →ₗ[S] M ⊗[R] R := AlgebraTensorModule.map LinearMap.id I.subtype
  letI e' : M ⊗[R] R →ₗ[S] M := AlgebraTensorModule.rid R S M
  exact AlgebraTensorModule.rid R S M ∘ₗ i

private noncomputable abbrev J (I : Ideal R) : Ideal S := LinearMap.range (auxRightMul R S S I)

private noncomputable abbrev auxIso [Module.Flat R S] {I : Ideal R} :
    S ⊗[R] I ≃ₗ[S] J R S I := by
  apply LinearEquiv.ofInjective (auxRightMul R S S I)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  exact (Module.Flat.iff_lTensor_injective' R S).mp inferInstance I

private noncomputable abbrev auxLTensor [Module.Flat R S] (I : Ideal R) :
    M ⊗[R] I →ₗ[S] M := by
  letI e1 : M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I) :=
    (AlgebraTensorModule.cancelBaseChange R S S M I).symm
  letI e2 : M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[S] (J R S I) :=
    TensorProduct.congr (LinearEquiv.refl S M) (auxIso R S)
  letI e3 : M ⊗[S] (J R S I) →ₗ[S] M ⊗[S] S := lTensor M (J R S I).subtype
  letI e4 : M ⊗[S] S →ₗ[S] M := TensorProduct.rid S M
  exact e4 ∘ₗ e3 ∘ₗ (e1 ≪≫ₗ e2)

private lemma auxLTensor_eq [Module.Flat R S] {I : Ideal R} :
    (auxLTensor R S M I : M ⊗[R] I →ₗ[R] M) =
    TensorProduct.rid R M ∘ₗ lTensor M (I.subtype) := by
  apply TensorProduct.ext'
  intro m x
  erw [TensorProduct.rid_tmul]
  simp

/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
theorem comp [Module.Flat R S] [Module.Flat S M] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [← EquivLike.comp_injective _ (TensorProduct.rid R M)]
  haveI h : TensorProduct.rid R M ∘ lTensor M (Submodule.subtype I) =
    TensorProduct.rid R M ∘ₗ lTensor M I.subtype := rfl
  simp only [h, ← auxLTensor_eq R S M, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
  exact (Module.Flat.iff_lTensor_injective' S M).mp inferInstance _

end Module.Flat
