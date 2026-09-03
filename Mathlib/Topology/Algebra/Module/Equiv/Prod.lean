/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Continuous linear equivalences on products of topological modules


## Notation
Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.

## Main Definitions
* `prodCongr`: `Equiv.prodCongr` as a continuous linear equivalence.
* `prodComm`: `LinearEquiv.prodComm` as a continuous linear equivalence.
* `prodAssoc`: `LinearEquiv.prodAssoc` as a continuous linear equivalence.
* `prodProdProdComm`: `LinearEquiv.prodProdProdComm` as a continuous linear equivalence.
* `prodUnique`: `Equiv.prodUnique` as a continuous linear equivalence.
* `uniqueProd`: `Equiv.uniqueProd` as a continuous linear equivalence.

-/

@[expose] public section

assert_not_exists TrivialStar

variable {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

namespace ContinuousLinearEquiv

section prodCongr

/-- Product of two continuous linear equivalences. The map comes from `Equiv.prodCongr`. -/
def prodCongr (e : M₁ ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) :
    (M₁ × M₃) ≃L[R] M₂ × M₄ where
  __ := e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]
theorem prodCongr_apply (e : M₁ ≃L[R] M₂)
    (e' : M₃ ≃L[R] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prodCongr (e : M₁ ≃L[R] M₂)
    (e' : M₃ ≃L[R] M₄) :
    (e.prodCongr e' : M₁ × M₃ →L[R] M₂ × M₄) = (e : M₁ →L[R] M₂).prodMap (e' : M₃ →L[R] M₄) :=
  rfl

@[simp]
theorem prodCongr_symm (e : M₁ ≃L[R] M₂)
    (e' : M₃ ≃L[R] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm :=
  rfl

end prodCongr

section prodComm

variable (R M₁ M₂)

set_option backward.defeqAttrib.useBackward true in
/-- Product of topological modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
def prodComm : (M₁ × M₂) ≃L[R] M₂ × M₁ where
  __ := LinearEquiv.prodComm R M₁ M₂

@[simp] lemma prodComm_symm : (prodComm R M₁ M₂).symm = prodComm R M₂ M₁ := rfl

/-- Composition of a map on a product with the exchange of the product factors -/
theorem _root_.ContinuousLinearMap.coprod_comp_prodComm
    [ContinuousAdd M₃] (f : M₁ →L[R] M₃) (g : M₂ →L[R] M₃) :
    f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₂ M₁ = g.coprod f := by
  ext <;> simp

end prodComm

section prodAssoc

variable (R M₁ M₂ M₃)

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
lemma prodAssoc_toLinearEquiv :
    (prodAssoc R M₁ M₂ M₃).toLinearEquiv = LinearEquiv.prodAssoc R M₁ M₂ M₃ := rfl

@[simp]
lemma coe_prodAssoc :
    (prodAssoc R M₁ M₂ M₃ : (M₁ × M₂) × M₃ → M₁ × M₂ × M₃) = Equiv.prodAssoc M₁ M₂ M₃ := rfl

@[simp]
lemma prodAssoc_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    prodAssoc R M₁ M₂ M₃ ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

@[simp]
lemma prodAssoc_symm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    (prodAssoc R M₁ M₂ M₃).symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃) := rfl

end prodAssoc

section prodProdProdComm

variable (R M₁ M₂ M₃ M₄)

/-- The product of topological modules is four-way commutative up to continuous linear isomorphism.
This is `LinearEquiv.prodProdProdComm` prodAssoc as a continuous linear equivalence. -/
def prodProdProdComm : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  toLinearEquiv := LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄

@[simp]
theorem prodProdProdComm_symm :
    (prodProdProdComm R M₁ M₂ M₃ M₄).symm = prodProdProdComm R M₁ M₃ M₂ M₄ :=
  rfl

@[simp]
lemma prodProdProdComm_toLinearEquiv :
    (prodProdProdComm R M₁ M₂ M₃ M₄).toLinearEquiv = LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄ :=
  rfl

@[simp]
lemma coe_prodProdProdComm :
    (prodProdProdComm R M₁ M₂ M₃ M₄ : (M₁ × M₂) × M₃ × M₄ → (M₁ × M₃) × M₂ × M₄) =
      Equiv.prodProdProdComm M₁ M₂ M₃ M₄ := rfl

@[simp]
lemma prodProdProdComm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄) :
    prodProdProdComm R M₁ M₂ M₃ M₄ ((p₁, p₂), p₃, p₄) = ((p₁, p₃), p₂, p₄) := rfl

end prodProdProdComm

section prodUnique

variable (R M₁ M₂) [Unique M₂]

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `M × N ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (M₁ × M₂) ≃L[R] M₁ where
  toLinearEquiv := LinearEquiv.prodUnique

@[simp]
lemma coe_prodUnique : (prodUnique R M₁ M₂).toEquiv = Equiv.prodUnique M₁ M₂ := rfl

@[simp]
lemma prodUnique_apply (x : M₁ × M₂) : prodUnique R M₁ M₂ x = x.1 := rfl

@[simp]
lemma prodUnique_symm_apply (x : M₁) : (prodUnique R M₁ M₂).symm x = (x, default) := rfl

end prodUnique

section uniqueProd

variable (R M₁ M₂) [Unique M₂]

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `N × M ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.uniqueProd` as a continuous linear equivalence. -/
def uniqueProd : (M₂ × M₁) ≃L[R] M₁ where
  toLinearEquiv := LinearEquiv.uniqueProd

@[simp]
lemma coe_uniqueProd : (uniqueProd R M₁ M₂).toEquiv = Equiv.uniqueProd M₁ M₂ := rfl

@[simp]
lemma uniqueProd_apply (x : M₂ × M₁) : uniqueProd R M₁ M₂ x = x.2 := rfl

@[simp]
lemma uniqueProd_symm_apply (x : M₁) : (uniqueProd R M₁ M₂).symm x = (default, x) := rfl

end uniqueProd

end ContinuousLinearEquiv
