/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.locally_constant.algebra
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`add_group`, etc)
on the type of locally constant functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X]

@[to_additive]
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[simp, to_additive]
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl
#align locally_constant.coe_one LocallyConstant.coe_one
#align locally_constant.coe_zero LocallyConstant.coe_zero

@[to_additive]
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl
#align locally_constant.one_apply LocallyConstant.one_apply
#align locally_constant.zero_apply LocallyConstant.zero_apply

@[to_additive]
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.IsLocallyConstant.inv⟩

@[simp, to_additive]
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑f⁻¹ = f⁻¹ :=
  rfl
#align locally_constant.coe_inv LocallyConstant.coe_inv
#align locally_constant.coe_neg LocallyConstant.coe_neg

@[to_additive]
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align locally_constant.inv_apply LocallyConstant.inv_apply
#align locally_constant.neg_apply LocallyConstant.neg_apply

@[to_additive]
instance [Mul Y] : Mul (LocallyConstant X Y)
    where mul f g := ⟨f * g, f.IsLocallyConstant.mul g.IsLocallyConstant⟩

@[simp, to_additive]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl
#align locally_constant.coe_mul LocallyConstant.coe_mul
#align locally_constant.coe_add LocallyConstant.coe_add

@[to_additive]
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl
#align locally_constant.mul_apply LocallyConstant.mul_apply
#align locally_constant.add_apply LocallyConstant.add_apply

@[to_additive]
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  { LocallyConstant.hasOne,
    LocallyConstant.hasMul with
    one_mul := by
      intros
      ext
      simp only [mul_apply, one_apply, one_mul]
    mul_one := by
      intros
      ext
      simp only [mul_apply, one_apply, mul_one] }

/-- `coe_fn` is a `monoid_hom`. -/
@[to_additive "`coe_fn` is an `add_monoid_hom`.", simps]
def coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y →* X → Y
    where
  toFun := coeFn
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.coe_fn_monoid_hom LocallyConstant.coeFnMonoidHom
#align locally_constant.coe_fn_add_monoid_hom LocallyConstant.coeFnAddMonoidHom

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive "The constant-function embedding, as an additive monoid hom.", simps]
def constMonoidHom [MulOneClass Y] : Y →* LocallyConstant X Y
    where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.const_monoid_hom LocallyConstant.constMonoidHom
#align locally_constant.const_add_monoid_hom LocallyConstant.constAddMonoidHom

instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  { LocallyConstant.hasZero,
    LocallyConstant.hasMul with
    zero_mul := by
      intros
      ext
      simp only [mul_apply, zero_apply, zero_mul]
    mul_zero := by
      intros
      ext
      simp only [mul_apply, zero_apply, mul_zero] }

instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.mulOneClass with }

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU
#align locally_constant.char_fn LocallyConstant.charFn

theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicator U 1 :=
  rfl
#align locally_constant.coe_char_fn LocallyConstant.coe_charFn

theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _
#align locally_constant.char_fn_eq_one LocallyConstant.charFn_eq_one

theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_not_mem _
#align locally_constant.char_fn_eq_zero LocallyConstant.charFn_eq_zero

theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h
#align locally_constant.char_fn_inj LocallyConstant.charFn_inj

end CharFn

@[to_additive]
instance [Div Y] : Div (LocallyConstant X Y)
    where div f g := ⟨f / g, f.IsLocallyConstant.div g.IsLocallyConstant⟩

@[to_additive]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl
#align locally_constant.coe_div LocallyConstant.coe_div
#align locally_constant.coe_sub LocallyConstant.coe_sub

@[to_additive]
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl
#align locally_constant.div_apply LocallyConstant.div_apply
#align locally_constant.sub_apply LocallyConstant.sub_apply

@[to_additive]
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) :=
  { LocallyConstant.hasMul with
    mul_assoc := by
      intros
      ext
      simp only [mul_apply, mul_assoc] }

instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.semigroup with }

@[to_additive]
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  { LocallyConstant.semigroup with
    mul_comm := by
      intros
      ext
      simp only [mul_apply, mul_comm] }

@[to_additive]
instance [Monoid Y] : Monoid (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.mulOneClass with mul := (· * ·) }

instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  { LocallyConstant.addMonoid,
    LocallyConstant.hasOne with
    natCast := fun n => const X n
    natCast_zero := by ext <;> simp [Nat.cast]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast] }

@[to_additive]
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) :=
  { LocallyConstant.commSemigroup, LocallyConstant.monoid with }

@[to_additive]
instance [Group Y] : Group (LocallyConstant X Y) :=
  { LocallyConstant.monoid, LocallyConstant.hasInv,
    LocallyConstant.hasDiv with
    mul_left_inv := by
      intros
      ext
      simp only [mul_apply, inv_apply, one_apply, mul_left_inv]
    div_eq_mul_inv := by
      intros
      ext
      simp only [mul_apply, inv_apply, div_apply, div_eq_mul_inv] }

@[to_additive]
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) :=
  { LocallyConstant.commMonoid, LocallyConstant.group with }

instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  { LocallyConstant.hasAdd,
    LocallyConstant.hasMul with
    left_distrib := by
      intros
      ext
      simp only [mul_apply, add_apply, mul_add]
    right_distrib := by
      intros
      ext
      simp only [mul_apply, add_apply, add_mul] }

instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.addCommMonoid, LocallyConstant.hasMul, LocallyConstant.distrib,
    LocallyConstant.mulZeroClass with }

instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocSemiring with }

instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.addMonoidWithOne,
    LocallyConstant.nonUnitalNonAssocSemiring with }

/-- The constant-function embedding, as a ring hom.  -/
@[simps]
def constRingHom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }
#align locally_constant.const_ring_hom LocallyConstant.constRingHom

instance [Semiring Y] : Semiring (LocallyConstant X Y) :=
  { LocallyConstant.nonAssocSemiring, LocallyConstant.monoid with }

instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalSemiring, LocallyConstant.commSemigroup with }

instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.commMonoid with }

instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.addCommGroup, LocallyConstant.hasMul, LocallyConstant.distrib,
    LocallyConstant.mulZeroClass with }

instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocRing with }

instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.nonUnitalNonAssocRing with }

instance [Ring Y] : Ring (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.addCommGroup with }

instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalCommSemiring, LocallyConstant.nonUnitalRing with }

instance [CommRing Y] : CommRing (LocallyConstant X Y) :=
  { LocallyConstant.commSemiring, LocallyConstant.ring with }

variable {R : Type _}

instance [SMul R Y] : SMul R (LocallyConstant X Y)
    where smul r f :=
    { toFun := r • f
      IsLocallyConstant := (f.IsLocallyConstant.comp ((· • ·) r) : _) }

@[simp]
theorem coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • f :=
  rfl
#align locally_constant.coe_smul LocallyConstant.coe_smul

theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl
#align locally_constant.smul_apply LocallyConstant.smul_apply

instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y)
    where
  toRingHom := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl
#align locally_constant.coe_algebra_map LocallyConstant.coe_algebraMap

end Algebra

end LocallyConstant

