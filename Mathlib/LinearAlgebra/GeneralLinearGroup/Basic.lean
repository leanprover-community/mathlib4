/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `Matrix.GeneralLinearGroup`

## Main definitions

* `LinearMap.GeneralLinearGroup`

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


variable (R M : Type*)

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- The group of invertible linear maps from `M` to itself -/
abbrev GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ

namespace GeneralLinearGroup

variable {R M}

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by simp
    right_inv := fun m ↦ show (f.val * f.inv) m = m by simp }

@[simp] lemma coe_toLinearEquiv (f : GeneralLinearGroup R M) :
    f.toLinearEquiv = (f : M → M) := rfl

theorem toLinearEquiv_mul (f g : GeneralLinearGroup R M) :
    (f * g).toLinearEquiv = f.toLinearEquiv * g.toLinearEquiv := by
  rfl

theorem toLinearEquiv_inv (f : GeneralLinearGroup R M) :
    (f⁻¹).toLinearEquiv = (f.toLinearEquiv)⁻¹ := by
  rfl

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ ↦ f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ ↦ f.symm_apply_apply _

@[simp] lemma coe_ofLinearEquiv (f : M ≃ₗ[R] M) :
    ofLinearEquiv f = (f : M → M) := rfl

theorem ofLinearEquiv_mul (f g : M ≃ₗ[R] M) :
    ofLinearEquiv (f * g) = ofLinearEquiv f * ofLinearEquiv g := by
  rfl

theorem ofLinearEquiv_inv (f : M ≃ₗ[R] M) :
    ofLinearEquiv (f⁻¹) = (ofLinearEquiv f)⁻¹ := by
  rfl

@[simp]
lemma ofLinearEquiv_smul (f : M ≃ₗ[R] M) (x : M) :
    ofLinearEquiv f • x = f x := rfl

variable (R M) in
/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  map_mul' x y := by ext; rfl

@[simp]
theorem generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f : M →ₗ[R] M) = f := by ext; rfl

@[simp]
theorem coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f) = (f : M → M) := rfl

section Functoriality

variable {R₁ R₂ R₃ M₁ M₂ M₃ : Type*}
  [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
  {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₁₃ σ₃₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

/-- A semilinear equivalence from `V` to `W` determines an isomorphism of general linear
groups. -/
def congrLinearEquiv (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    GeneralLinearGroup R₁ M₁ ≃* GeneralLinearGroup R₂ M₂ :=
  Units.mapEquiv (LinearEquiv.conjRingEquiv e₁₂).toMulEquiv

@[simp] lemma congrLinearEquiv_apply (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : GeneralLinearGroup R₁ M₁) :
    congrLinearEquiv e₁₂ g = ofLinearEquiv (e₁₂.symm.trans <| g.toLinearEquiv.trans e₁₂) :=
  rfl

@[simp] lemma congrLinearEquiv_symm (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    (congrLinearEquiv e₁₂).symm = congrLinearEquiv e₁₂.symm :=
  rfl

@[simp]
lemma congrLinearEquiv_trans
    {N₁ N₂ N₃ : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) = congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

/-- Stronger form of `congrLinearEquiv.trans` applying to semilinear maps. Not a simp lemma as
`σ₁₃` and `σ₃₁` cannot be inferred from the LHS. -/
lemma congrLinearEquiv_trans' (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) =
      congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

@[simp]
lemma congrLinearEquiv_refl :
    congrLinearEquiv (LinearEquiv.refl R₁ M₁) = MulEquiv.refl (GeneralLinearGroup R₁ M₁) :=
  rfl

end Functoriality

end GeneralLinearGroup

end LinearMap
