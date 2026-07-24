module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Continuous linear equivalences


## Notation
Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.

## Main Definitions
* `prodCongr`: `Equiv.prodCongr` as a continuous linear equivalence.
* `prodComm`: `LinearEquiv.prodComm` as a continuous linear equivalence.
* `prodAssoc`: `LinearEquiv.prodAssoc` as a continuous linear equivalence.
* `prodProdProdComm`: `LinearEquiv.prodProdProdComm` as a continuous linear equivalence.
* `prodUnique`: `Equiv.uniqueProd` as a continuous linear equivalence.

## Main Results
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise
open scoped Ring

universe u v w u'

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

namespace ContinuousLinearEquiv

/-- Product of two continuous linear equivalences. The map comes from `Equiv.prodCongr`. -/
def prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ where
  __ := e.toLinearEquiv.prodCongr e'.toLinearEquiv

@[simp, norm_cast]
theorem prodCongr_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prodCongr e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prodMap (e' : M₃ →L[R₁] M₄) :=
  rfl

@[simp]
theorem prodCongr_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm :=
  rfl

variable (R₁ M₁ M₂)

set_option backward.defeqAttrib.useBackward true in
/-- Product of topological modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ where
  __ := LinearEquiv.prodComm R₁ M₁ M₂

@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

section prodAssoc

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

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

variable (R M₁ M₂ M₃ M₄ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]

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

variable (R M N : Type*) [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace N] [AddCommMonoid N]
  [Unique N] [Module R M] [Module R N]

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `M × N ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (M × N) ≃L[R] M where
  toLinearEquiv := LinearEquiv.prodUnique

@[simp]
lemma coe_prodUnique : (prodUnique R M N).toEquiv = Equiv.prodUnique M N := rfl

@[simp]
lemma prodUnique_apply (x : M × N) : prodUnique R M N x = x.1 := rfl

@[simp]
lemma prodUnique_symm_apply (x : M) : (prodUnique R M N).symm x = (x, default) := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence `N × M ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.uniqueProd` as a continuous linear equivalence. -/
def uniqueProd : (N × M) ≃L[R] M where
  toLinearEquiv := LinearEquiv.uniqueProd

@[simp]
lemma coe_uniqueProd : (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N := rfl

@[simp]
lemma uniqueProd_apply (x : N × M) : uniqueProd R M N x = x.2 := rfl

@[simp]
lemma uniqueProd_symm_apply (x : M) : (uniqueProd R M N).symm x = (default, x) := rfl

end prodUnique

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- Composition of a map on a product with the exchange of the product factors -/
theorem coprod_comp_prodComm (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Module R M₁] [Module R M₂] [TopologicalSpace M] [ContinuousAdd M] (f : M₂ →L[R] M)
    (g : M₁ →L[R] M) : f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₁ M₂ = g.coprod f := by
  ext <;> simp

end ContinuousLinearMap
