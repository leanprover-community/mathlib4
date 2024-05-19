/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Hom

/-!
# Isomorphisms of `k`-linear `G`-representations

This file defines bundled isomorphisms of monoid representations. We largely mimic
`Mathlib/Algebra/Module/Equiv.lean`.

## Main definitions

* `RepresentationEquiv ρ τ`: given `k`-linear `G`-representations `ρ, τ` of `k`-modules
`V, W` respectively, this is the type of `k`-linear isomorphisms between `V` and `W`
compatible with the representations.

## Notations

* `ρ ≃ₑₗ τ`: representation isomorphism between `(V, ρ)` and `(W, τ)`.

-/

open BigOperators

universe u v w

variable {k G V W X : Type*}

open Representation

/-- An equivalence of representations is an invertible representation homomorphism. -/
structure RepresentationEquiv [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [Module k V] [Module k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    extends ρ →ₑₗ τ, V ≃ₗ[k] W where

attribute [nolint docBlame] RepresentationEquiv.toRepresentationHom
attribute [nolint docBlame] RepresentationEquiv.toLinearEquiv

@[inherit_doc RepresentationEquiv]
notation:50 ρ " ≃ₑₗ " τ => RepresentationEquiv ρ τ

/-- `RepresentationEquivClass F ρ τ` asserts `F` is a type of bundled representation equivalences
from `(V, ρ)` to `(W, τ)`.  -/
class RepresentationEquivClass (F : Type*) {k G V W : outParam Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [AddCommMonoid W] [Module k V] [Module k W]
    (ρ : outParam (Representation k G V)) (τ : outParam (Representation k G W)) [EquivLike F V W]
    extends RepresentationHomClass F ρ τ, SemilinearEquivClass F (RingHom.id k) V W : Prop

namespace RepresentationEquivClass

variable {F k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module k V] [Module k W] {ρ : Representation k G V} {τ : Representation k G W}

/-- Reinterpret an element of a type of representation equivalences as a representation equivalence. -/
@[coe]
def toRepresentationEquiv [EquivLike F V W] [RepresentationEquivClass F ρ τ] (f : F) : ρ ≃ₑₗ τ :=
  { (f : ρ →ₑₗ τ), (f : V ≃ₗ[k] W) with }

/-- Reinterpret an element of a type of representation equivalences as a representation equivalence. -/
instance instCoeToRepresentationEquiv
    [EquivLike F V W] [RepresentationEquivClass F ρ τ] : CoeHead F (ρ ≃ₑₗ τ) where
  coe f := toRepresentationEquiv f

end RepresentationEquivClass

namespace RepresentationEquiv

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [AddCommMonoid X] [Module k V] [Module k W] [Module k X]
  {ρ : Representation k G V} {τ : Representation k G W} {η : Representation k G X}

section

/-- The equivalence of types underlying a representation equivalence. -/
def toEquiv : (ρ ≃ₑₗ τ) → V ≃ W := fun f => f.toLinearEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (ρ ≃ₑₗ τ) → V ≃ W) :=
  fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h =>
    (RepresentationEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨RepresentationHom.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
theorem toEquiv_inj {e₁ e₂ : ρ ≃ₑₗ τ} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toRepresentationHom_injective :
    Function.Injective (toRepresentationHom : (ρ ≃ₑₗ τ) → ρ →ₑₗ τ) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| RepresentationHom.congr_fun H

instance : EquivLike (ρ ≃ₑₗ τ) V W where
  inv := RepresentationEquiv.invFun
  coe_injective' _ _ h _ := toRepresentationHom_injective (DFunLike.coe_injective h)
  left_inv := RepresentationEquiv.left_inv
  right_inv := RepresentationEquiv.right_inv

instance : FunLike (ρ ≃ₑₗ τ) V W where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

instance : RepresentationEquivClass (ρ ≃ₑₗ τ) ρ τ where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
  comm := (·.comm)

@[simp, norm_cast]
theorem toRepresentationHom_inj {e₁ e₂ : ρ ≃ₑₗ τ} : (↑e₁ : ρ →ₑₗ τ) = e₂ ↔ e₁ = e₂ :=
  toRepresentationHom_injective.eq_iff

@[simp]
theorem coe_mk {f h h₀ h₁ h₂ h₃ h₄} :
    (⟨⟨⟨⟨f, h⟩, h₀⟩, h₁⟩, h₂, h₃, h₄⟩ : ρ ≃ₑₗ τ) = f := rfl

end

section

/-- See Note [custom simps projection] -/
def Simps.apply (f : ρ ≃ₑₗ τ) : V → W := f

def Simps.toRepresentationHom (f : ρ ≃ₑₗ τ) : ρ →ₑₗ τ := f

initialize_simps_projections RepresentationEquiv (toFun → apply,
  toRepresentationHom → toRepresentationHom)

end

variable (e : ρ ≃ₑₗ τ)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : ρ →ₑₗ τ) = e :=
  rfl

@[simp]
theorem toLinearEquiv_eq_coe (f : ρ ≃ₑₗ τ) : f.toLinearEquiv = f :=
  rfl

@[simp]
theorem toRepresentationHom_eq_coe (f : ρ ≃ₑₗ τ) : f.toRepresentationHom = f :=
  rfl

@[simp]
theorem coe_toLinearEquiv : ⇑(e : V ≃ₗ[k] W) = e :=
  rfl

@[simp]
theorem coe_toRepresentationHom : ⇑(e : ρ →ₑₗ τ) = e :=
  rfl

theorem toLinearEquiv_toLinearMap : ((e : V ≃ₗ[k] W) : V →ₗ[k] W) = (e : ρ →ₑₗ τ) :=
  rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  DFunLike.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : V) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (ρ) in
/-- The identity map is a representation equivalence. -/
@[refl, simps! toRepresentationHom apply]
def refl : ρ ≃ₑₗ ρ :=
  { RepresentationHom.id ρ, LinearEquiv.refl k V with }

end

@[simp]
theorem refl_toLinearEquiv : refl ρ = LinearEquiv.refl k V := rfl

/-- Representation equivalences are symmetric. -/
@[symm]
def symm (e : ρ ≃ₑₗ τ) : τ ≃ₑₗ ρ :=
  { (e : V ≃ₗ[k] W).symm with
    comm := fun g => by ext; simp [LinearEquiv.symm_apply_eq, ← coe_toLinearEquiv] }

@[simp]
theorem symm_toLinearEquiv (e : ρ ≃ₑₗ τ) :
    e.symm = (e : V ≃ₗ[k] W).symm := rfl

@[simp]
theorem symm_toRepresentationHom (e : ρ ≃ₑₗ τ) :
    ((e.symm : τ →ₑₗ ρ) : W →ₗ[k] V) = (e : V ≃ₗ[k] W).symm := rfl

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : ρ ≃ₑₗ τ) : W → V :=
  e.symm

initialize_simps_projections RepresentationEquiv (invFun → symm_apply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl

variable {e₁₂ : ρ ≃ₑₗ τ} {e₂₃ : τ ≃ₑₗ η}

/-- Representation equivalences are transitive. -/
@[trans, simps! toRepresentationHom apply]
def trans (e₁₂ : ρ ≃ₑₗ τ) (e₂₃ : τ ≃ₑₗ η) : ρ ≃ₑₗ η :=
  { (e₂₃ : τ →ₑₗ η).comp (e₁₂ : ρ →ₑₗ τ), e₁₂.toLinearEquiv ≪≫ₗ e₂₃.toLinearEquiv with }

@[simp]
theorem trans_toLinearEquiv :
    (e₁₂.trans e₂₃ : V ≃ₗ[k] X) = (e₁₂ : V ≃ₗ[k] W) ≪≫ₗ e₂₃ := rfl

@[simp]
theorem coe_toEquiv_trans : (e₁₂ : V ≃ W).trans e₂₃ = (e₁₂.trans e₂₃ : V ≃ X) :=
  rfl

end RepresentationEquiv
namespace Representation
section tprod

variable [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
variable [Module k V] [Module k W] [Module k X]
variable {ρ : Representation k G V} {τ : Representation k G W} {η : Representation k G X}

variable (ρ) in
noncomputable def tprodTrivial : ρ.tprod (trivial k G k) ≃ₑₗ ρ :=
  { TensorProduct.rid _ _ with
    comm := fun _ => by ext; simp }

@[simp]
theorem tprodTrivial_toLinearEquiv :
  tprodTrivial ρ = TensorProduct.rid k V := rfl

@[simp]
theorem tprodTrivial_tmul (v : V) (r : k) :
    tprodTrivial ρ (v ⊗ₜ r) = r • v :=
  TensorProduct.rid_tmul _ _

variable (ρ) in
noncomputable def trivialTProd : (trivial k G k).tprod ρ ≃ₑₗ ρ :=
  { TensorProduct.lid _ _ with
    comm := fun _ => by ext; simp }

@[simp]
theorem trivialTProd_toLinearEquiv :
  trivialTProd ρ = TensorProduct.lid k V := rfl

@[simp]
theorem trivialTProd_tmul (v : V) (r : k) :
    trivialTProd ρ (r ⊗ₜ v) = r • v :=
  TensorProduct.lid_tmul _ _

variable (ρ τ η) in
noncomputable def tprodAssoc : (ρ.tprod τ).tprod η ≃ₑₗ ρ.tprod (τ.tprod η) :=
  { TensorProduct.assoc _ _ _ _ with
    comm := fun _ => by ext; simp }

@[simp]
theorem tprodAssoc_toLinearEquiv :
  tprodAssoc ρ τ η = TensorProduct.assoc k V W X := rfl

@[simp]
theorem tprodAssoc_tmul (v : V) (w : W) (x : X) :
    tprodAssoc ρ τ η ((v ⊗ₜ w) ⊗ₜ x) = (v ⊗ₜ (w ⊗ₜ x)) :=
  TensorProduct.assoc_tmul _ _ _

variable (ρ τ) in
noncomputable def tprodComm : (ρ.tprod τ) ≃ₑₗ (τ.tprod ρ) :=
  { TensorProduct.comm _ _ _ with
    comm := fun _ => by ext; simp }

@[simp]
theorem tprodComm_toLinearEquiv :
  tprodComm ρ τ = TensorProduct.comm k V W := rfl

@[simp]
theorem tprodComm_tmul (v : V) (w : W) :
    tprodComm ρ τ (v ⊗ₜ w) = (w ⊗ₜ v) :=
  TensorProduct.comm_tmul _ _ _ _ _

end tprod
end Representation
