/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.WithOne.Defs

#align_import algebra.group.with_one.basic from "leanprover-community/mathlib"@"4dc134b97a3de65ef2ed881f3513d56260971562"

/-!
# More operations on `WithOne` and `WithZero`

This file defines various bundled morphisms on `WithOne` and `WithZero`
that were not available in `Algebra/Group/WithOne/Defs`.

## Main definitions

* `WithOne.lift`, `WithZero.lift`
* `WithOne.map`, `WithZero.map`
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

@[to_additive]
instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) :=
  { WithOne.inv with
    inv_inv := fun a =>
      (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

section

-- Porting note: the workaround described below doesn't seem to be a problem even with
-- semireducible transparency
-- workaround: we make `WithOne`/`WithZero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
/-- `WithOne.coe` as a bundled morphism -/
@[to_additive (attr := simps apply) "`WithZero.coe` as a bundled morphism"]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' _ _ := rfl
#align with_one.coe_mul_hom WithOne.coeMulHom
#align with_zero.coe_add_hom WithZero.coeAddHom
#align with_one.coe_mul_hom_apply WithOne.coeMulHom_apply
#align with_zero.coe_add_hom_apply WithZero.coeAddHom_apply

end

section lift

-- Porting note: these were never marked with `irreducible` when they were defined.
-- attribute [local semireducible] WithOne WithZero

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homomorphism. -/
@[to_additive "Lift an add semigroup homomorphism `f` to a bundled add monoid homomorphism."]
def lift : (α →ₙ* β) ≃ (WithOne α →* β) where
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f, map_one' := rfl,
      map_mul' := fun x y => WithOne.cases_on x (by rw [one_mul]; exact (one_mul _).symm)
        (fun x => WithOne.cases_on y (by rw [mul_one]; exact (mul_one _).symm)
          (fun y => f.map_mul x y)) }
  invFun F := F.toMulHom.comp coeMulHom
  left_inv f := MulHom.ext fun x => rfl
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun x => rfl)
-- Porting note: the above proofs were broken because they were parenthesized wrong by mathport?
#align with_one.lift WithOne.lift
#align with_zero.lift WithZero.lift

variable (f : α →ₙ* β)

@[to_additive (attr := simp)]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl
#align with_one.lift_coe WithOne.lift_coe
#align with_zero.lift_coe WithZero.lift_coe

-- Porting note (#11119): removed `simp` attribute to appease `simpNF` linter.
@[to_additive]
theorem lift_one : lift f 1 = 1 :=
  rfl
#align with_one.lift_one WithOne.lift_one
#align with_zero.lift_zero WithZero.lift_zero

@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm
#align with_one.lift_unique WithOne.lift_unique
#align with_zero.lift_unique WithZero.lift_unique

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `WithOne α` to `WithOne β` -/
@[to_additive "Given an additive map from `α → β` returns an add monoid homomorphism from
`WithZero α` to `WithZero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)
#align with_one.map WithOne.map
#align with_zero.map WithZero.map

@[to_additive (attr := simp)]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  rfl
#align with_one.map_coe WithOne.map_coe
#align with_zero.map_coe WithZero.map_coe

@[to_additive (attr := simp)]
theorem map_id : map (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext x
  induction x <;> rfl
#align with_one.map_id WithOne.map_id
#align with_zero.map_id WithZero.map_id

@[to_additive]
theorem map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) : map g (map f x) = map (g.comp f) x := by
  induction x <;> rfl
#align with_one.map_map WithOne.map_map
#align with_zero.map_map WithZero.map_map

@[to_additive (attr := simp)]
theorem map_comp (f : α →ₙ* β) (g : β →ₙ* γ) : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun x => (map_map f g x).symm
#align with_one.map_comp WithOne.map_comp
#align with_zero.map_comp WithZero.map_comp

-- Porting note: this used to have `@[simps apply]` but it was generating lemmas which
-- weren't in simp normal form.
/-- A version of `Equiv.optionCongr` for `WithOne`. -/
@[to_additive (attr := simps apply) "A version of `Equiv.optionCongr` for `WithZero`."]
def _root_.MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with
    toFun := map e.toMulHom, invFun := map e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }
#align mul_equiv.with_one_congr MulEquiv.withOneCongr
#align add_equiv.with_zero_congr AddEquiv.withZeroCongr
#align mul_equiv.with_one_congr_apply MulEquiv.withOneCongr_apply
#align add_equiv.with_zero_congr_apply AddEquiv.withZeroCongr_apply

-- Porting note: for this declaration and the two below I added the `to_additive` attribute because
-- it seemed to be missing from mathlib3, hence the lack of additive `#align`s.
@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective map_id
#align mul_equiv.with_one_congr_refl MulEquiv.withOneCongr_refl

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl
#align mul_equiv.with_one_congr_symm MulEquiv.withOneCongr_symm

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (map_comp _ _).symm
#align mul_equiv.with_one_congr_trans MulEquiv.withOneCongr_trans

end Map

end WithOne
