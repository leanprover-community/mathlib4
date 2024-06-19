/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs

#align_import algebra.hom.group from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Additional lemmas about monoid and group homomorphisms

-/

-- `NeZero` cannot be additivised, hence its theory should be developed outside of the
-- `Algebra.Group` folder.
assert_not_exists NeZero

variable {α β M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

section CommMonoid
variable [CommMonoid α]

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps) "Multiplication by a natural `n` on a commutative additive monoid,
considered as a morphism of additive monoids."]
def powMonoidHom (n : ℕ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n
#align pow_monoid_hom powMonoidHom
#align nsmul_add_monoid_hom nsmulAddMonoidHom
#align pow_monoid_hom_apply powMonoidHom_apply
#align nsmul_add_monoid_hom_apply nsmulAddMonoidHom_apply

end CommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps) "Multiplication by an integer `n` on a commutative additive group,
considered as an additive group homomorphism."]
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n
#align zpow_group_hom zpowGroupHom
#align zsmul_add_group_hom zsmulAddGroupHom
#align zpow_group_hom_apply zpowGroupHom_apply
#align zsmul_add_group_hom_apply zsmulAddGroupHom_apply

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive "Negation on a commutative additive group, considered as an additive monoid
homomorphism."]
def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv
#align inv_monoid_hom invMonoidHom
#align neg_add_monoid_hom negAddMonoidHom

@[simp]
theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv := rfl
#align coe_inv_monoid_hom coe_invMonoidHom

@[simp]
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl
#align inv_monoid_hom_apply invMonoidHom_apply

end DivisionCommMonoid

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive "Given two additive morphisms `f`, `g` to an additive commutative semigroup,
`f + g` is the additive morphism sending `x` to `f x + g x`."]
instance [Mul M] [CommSemigroup N] : Mul (M →ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]
theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl
#align mul_hom.mul_apply MulHom.mul_apply
#align add_hom.add_apply AddHom.add_apply

@[to_additive]
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
#align mul_hom.mul_comp MulHom.mul_comp
#align add_hom.add_comp AddHom.add_comp

@[to_additive]
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]
#align mul_hom.comp_mul MulHom.comp_mul
#align add_hom.comp_add AddHom.comp_add

end MulHom

namespace MonoidHom
section Group
variable [Group G] [CommGroup H]

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`.  -/
@[to_additive
  "A homomorphism from an additive group to an additive monoid is injective iff
  its kernel is trivial. For the iff statement on the triviality of the kernel,
  see `injective_iff_map_eq_zero'`."]
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h x => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_self, map_one]⟩
#align injective_iff_map_eq_one injective_iff_map_eq_one
#align injective_iff_map_eq_zero injective_iff_map_eq_zero

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
  "A homomorphism from an additive group to an additive monoid is injective iff its
  kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
  `injective_iff_map_eq_zero`."]
theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  (injective_iff_map_eq_one f).trans <|
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩
#align injective_iff_map_eq_one' injective_iff_map_eq_one'
#align injective_iff_map_eq_zero' injective_iff_map_eq_zero'

variable [MulOneClass M]

/-- Makes a group homomorphism from a proof that the map preserves right division
`fun x y => x * y⁻¹`. See also `MonoidHom.of_map_div` for a version using `fun x y => x / y`.
-/
@[to_additive
  "Makes an additive group homomorphism from a proof that the map preserves
  the operation `fun a b => a + -b`. See also `AddMonoidHom.ofMapSub` for a version using
  `fun a b => a - b`."]
def ofMapMulInv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_right_inv, one_mul, inv_inv] }
#align monoid_hom.of_map_mul_inv MonoidHom.ofMapMulInv
#align add_monoid_hom.of_map_add_neg AddMonoidHom.ofMapAddNeg

@[to_additive (attr := simp)]
theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  ↑(ofMapMulInv f map_div) = f := rfl
#align monoid_hom.coe_of_map_mul_inv MonoidHom.coe_of_map_mul_inv
#align add_monoid_hom.coe_of_map_add_neg AddMonoidHom.coe_of_map_add_neg

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive "Define a morphism of additive groups given a map which respects difference."]
def ofMapDiv {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)
#align monoid_hom.of_map_div MonoidHom.ofMapDiv
#align add_monoid_hom.of_map_sub AddMonoidHom.ofMapSub

@[to_additive (attr := simp)]
theorem coe_of_map_div {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ↑(ofMapDiv f hf) = f := rfl
#align monoid_hom.coe_of_map_div MonoidHom.coe_of_map_div
#align add_monoid_hom.coe_of_map_sub AddMonoidHom.coe_of_map_sub

end Group

section Mul
variable [MulOneClass M] [CommMonoid N]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance mul : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := show f 1 * g 1 = 1 by simp,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.add

@[to_additive (attr := simp)] lemma mul_apply (f g : M →* N) (x : M) : (f * g) x = f x * g x := rfl
#align monoid_hom.mul_apply MonoidHom.mul_apply
#align add_monoid_hom.add_apply AddMonoidHom.add_apply

@[to_additive]
lemma mul_comp [MulOneClass P] (g₁ g₂ : M →* N) (f : P →* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
#align monoid_hom.mul_comp MonoidHom.mul_comp
#align add_monoid_hom.add_comp AddMonoidHom.add_comp

@[to_additive]
lemma comp_mul [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext; simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]
#align monoid_hom.comp_mul MonoidHom.comp_mul
#align add_monoid_hom.comp_add AddMonoidHom.comp_add

end Mul

section InvDiv
variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive "If `f` is an additive monoid homomorphism to an additive commutative group,
then `-f` is the homomorphism sending `x` to `-(f x)`."]
instance : Inv (M →* G) where
  inv f := mk' (fun g ↦ (f g)⁻¹) fun a b ↦ by simp_rw [← mul_inv, f.map_mul]

@[to_additive (attr := simp)] lemma inv_apply (f : M →* G) (x : M) : f⁻¹ x = (f x)⁻¹ := rfl
#align monoid_hom.inv_apply MonoidHom.inv_apply
#align add_monoid_hom.neg_apply AddMonoidHom.neg_apply

@[to_additive (attr := simp)]
theorem inv_comp (φ : N →* G) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl
#align monoid_hom.inv_comp MonoidHom.inv_comp
#align add_monoid_hom.neg_comp AddMonoidHom.neg_comp

@[to_additive (attr := simp)]
theorem comp_inv (φ : G →* H) (ψ : M →* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, map_inv, coe_comp]
#align monoid_hom.comp_inv MonoidHom.comp_inv
#align add_monoid_hom.comp_neg AddMonoidHom.comp_neg

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive "If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`."]
instance : Div (M →* G) where
  div f g := mk' (fun x ↦ f x / g x) fun a b ↦ by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

@[to_additive (attr := simp)] lemma div_apply (f g : M →* G) (x : M) : (f / g) x = f x / g x := rfl
#align monoid_hom.div_apply MonoidHom.div_apply
#align add_monoid_hom.sub_apply AddMonoidHom.sub_apply

@[to_additive (attr := simp)]
lemma div_comp (f g : N →* G) (h : M →* N) : (f / g).comp h = f.comp h / g.comp h := rfl

@[to_additive (attr := simp)]
lemma comp_div (f : G →* H) (g h : M →* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext; simp only [Function.comp_apply, div_apply, map_div, coe_comp]

end InvDiv

end MonoidHom
