/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.WithOne.Defs

/-!
# More operations on `WithOne` and `WithZero`

This file defines various bundled morphisms on `WithOne` and `WithZero`
that were not available in `Algebra/Group/WithOne/Defs`.

## Main definitions

* `WithOne.lift`, `WithZero.lift`
* `WithOne.map`, `WithZero.map`
-/

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

@[to_additive]
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) where
  inv_inv a := (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id]

section

/-- `WithOne.coe` as a bundled morphism -/
@[to_additive (attr := simps apply) /-- `WithZero.coe` as a bundled morphism -/]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' _ _ := rfl

end

section lift

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homomorphism. -/
@[to_additive /--
Lift an additive semigroup homomorphism `f` to a bundled additive monoid homomorphism. -/]
def lift : (α →ₙ* β) ≃ (WithOne α →* β) where
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f, map_one' := rfl,
      map_mul' := fun x y => WithOne.cases_on x (by rw [one_mul]; exact (one_mul _).symm)
        (fun x => WithOne.cases_on y (by rw [mul_one]; exact (mul_one _).symm)
          (fun y => f.map_mul x y)) }
  invFun F := F.toMulHom.comp coeMulHom
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun _ => rfl)

variable (f : α →ₙ* β)

@[to_additive (attr := simp)]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl

@[to_additive (attr := simp)]
theorem lift_one : lift f 1 = 1 :=
  rfl

@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `WithOne α` to `WithOne β` -/
@[to_additive /-- Given an additive map from `α → β` returns an additive monoid homomorphism from
`WithZero α` to `WithZero β` -/]
def mapMulHom (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)

@[to_additive (attr := simp)]
theorem mapMulHom_coe (f : α →ₙ* β) (a : α) : mapMulHom f (a : WithOne α) = f a :=
  rfl

@[to_additive (attr := simp)]
theorem mapMulHom_id : mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext x
  induction x <;> rfl

@[deprecated (since := "2025-08-26")]
alias map_id := mapMulHom_id
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_id := WithZero.mapAddHom_id

@[to_additive]
theorem mapMulHom_injective {f : α →ₙ* β} (hf : Function.Injective f) :
    Function.Injective (mapMulHom f)
  | none, none, _ => rfl
  | (a₁ : α), (a₂ : α), H => by simpa [hf.eq_iff] using H

@[deprecated (since := "2025-08-26")]
alias map_injective := mapMulHom_injective
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_injective := WithZero.mapAddHom_injective

@[to_additive]
theorem mapMulHom_injective' :
    Function.Injective (WithOne.mapMulHom (α := α) (β := β)) :=
  fun f g h ↦ MulHom.ext fun x ↦ coe_injective <| by simp only [← mapMulHom_coe, h]

@[deprecated (since := "2025-08-26")]
alias map_injective' := mapMulHom_injective'
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_injective' := WithZero.mapAddHom_injective'

@[to_additive (attr := simp)]
theorem mapMulHom_inj {f g : α →ₙ* β} : mapMulHom f = mapMulHom g ↔ f = g :=
  mapMulHom_injective'.eq_iff

@[deprecated (since := "2025-08-26")]
alias map_inj := mapMulHom_inj
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_inj := WithZero.mapAddHom_inj

@[to_additive]
theorem mapMulHom_mapMulHom (f : α →ₙ* β) (g : β →ₙ* γ) (x) :
    mapMulHom g (mapMulHom f x) = mapMulHom (g.comp f) x := by
  induction x <;> rfl

@[deprecated (since := "2025-08-26")]
alias map_map := mapMulHom_mapMulHom
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_map := WithZero.mapAddHom_mapAddHom

@[to_additive (attr := simp)]
theorem mapMulHom_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
    mapMulHom (g.comp f) = (mapMulHom g).comp (mapMulHom f) :=
  MonoidHom.ext fun x => (mapMulHom_mapMulHom f g x).symm

@[deprecated (since := "2025-08-26")]
alias map_comp := mapMulHom_comp
@[deprecated (since := "2025-08-26")]
alias _root_.WithZero.map_comp := WithZero.mapAddHom_comp

/-- A version of `Equiv.optionCongr` for `WithOne`. -/
@[to_additive (attr := simps apply) /-- A version of `Equiv.optionCongr` for `WithZero`. -/]
def _root_.MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { mapMulHom e.toMulHom with
    toFun := mapMulHom e.toMulHom, invFun := mapMulHom e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective mapMulHom_id

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (mapMulHom_comp _ _).symm

end Map

end WithOne
