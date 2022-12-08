/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathbin.Algebra.Group.WithOne.Defs
import Mathbin.Algebra.Hom.Equiv.Basic

/-!
# More operations on `with_one` and `with_zero`

This file defines various bundled morphisms on `with_one` and `with_zero`
that were not available in `algebra/group/with_one/defs`.

## Main definitions

* `with_one.lift`, `with_zero.lift`
* `with_one.map`, `with_zero.map`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

section

-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coeMulHom [Mul α] : α →ₙ* WithOne α where 
  toFun := coe
  map_mul' x y := rfl
#align with_one.coe_mul_hom WithOne.coeMulHom

end

section lift

attribute [local semireducible] WithOne WithZero

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift :
    (α →ₙ* β) ≃
      (WithOne α →*
        β) where 
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f, map_one' := rfl,
      map_mul' := fun x y =>
        (WithOne.cases_on x
            (by 
              rw [one_mul]
              exact (one_mul _).symm))
          fun x =>
          (WithOne.cases_on y
              (by 
                rw [mul_one]
                exact (mul_one _).symm))
            fun y => f.map_mul x y }
  invFun F := F.toMulHom.comp coeMulHom
  left_inv f := MulHom.ext fun x => rfl
  right_inv F := MonoidHom.ext fun x => (WithOne.cases_on x F.map_one.symm) fun x => rfl
#align with_one.lift WithOne.lift

variable (f : α →ₙ* β)

@[simp, to_additive]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl
#align with_one.lift_coe WithOne.lift_coe

@[simp, to_additive]
theorem lift_one : lift f 1 = 1 :=
  rfl
#align with_one.lift_one WithOne.lift_one

@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm
#align with_one.lift_unique WithOne.lift_unique

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive
      "Given an additive map from `α → β` returns an add_monoid homomorphism\n  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)
#align with_one.map WithOne.map

@[simp, to_additive]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  lift_coe _ _
#align with_one.map_coe WithOne.map_coe

@[simp, to_additive]
theorem map_id : map (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_id WithOne.map_id

@[to_additive]
theorem map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) : map g (map f x) = map (g.comp f) x := by
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_map WithOne.map_map

@[simp, to_additive]
theorem map_comp (f : α →ₙ* β) (g : β →ₙ* γ) : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun x => (map_map f g x).symm
#align with_one.map_comp WithOne.map_comp

/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with toFun := map e.toMulHom, invFun := map e.symm.toMulHom,
    left_inv := fun x => (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp,
    right_inv := fun x =>
      (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp }
#align mul_equiv.with_one_congr MulEquiv.withOneCongr

@[simp]
theorem MulEquiv.with_one_congr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.to_monoid_hom_injective map_id
#align mul_equiv.with_one_congr_refl MulEquiv.with_one_congr_refl

@[simp]
theorem MulEquiv.with_one_congr_symm (e : α ≃* β) : e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl
#align mul_equiv.with_one_congr_symm MulEquiv.with_one_congr_symm

@[simp]
theorem MulEquiv.with_one_congr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.to_monoid_hom_injective (map_comp _ _).symm
#align mul_equiv.with_one_congr_trans MulEquiv.with_one_congr_trans

end Map

end WithOne

