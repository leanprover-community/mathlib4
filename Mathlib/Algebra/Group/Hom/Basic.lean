/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.NeZero

#align_import algebra.hom.group from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Additional lemmas about monoid and group homomorphisms

-/


variable {α β M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

namespace NeZero

theorem of_map {R M} [Zero R] [Zero M] [NDFunLike F R M] [ZeroHomClass F R M]
    (f : F) {r : R} [neZero : NeZero (f r)] : NeZero r :=
  ⟨fun h => ne (f r) <| by rw [h]; exact ZeroHomClass.map_zero f⟩
#align ne_zero.of_map NeZero.of_map

theorem of_injective {R M} [Zero R] {r : R} [NeZero r] [Zero M] [NDFunLike F R M]
    [ZeroHomClass F R M] {f : F}
    (hf : Function.Injective f) : NeZero (f r) :=
  ⟨by
    rw [← ZeroHomClass.map_zero f]
    exact hf.ne NeZero.out⟩
#align ne_zero.of_injective NeZero.of_injective

end NeZero

section DivisionCommMonoid

variable [DivisionCommMonoid α]

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
        intros
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

variable [Group G] [CommGroup H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance mul {M N} [MulOneClass M] [CommMonoid N] : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := show f 1 * g 1 = 1 by simp,
      map_mul' := fun x y => by
        intros
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.add

@[to_additive (attr := simp)]
theorem mul_apply {M N} [MulOneClass M] [CommMonoid N] (f g : M →* N) (x : M) :
    (f * g) x = f x * g x := rfl
#align monoid_hom.mul_apply MonoidHom.mul_apply
#align add_monoid_hom.add_apply AddMonoidHom.add_apply

@[to_additive]
theorem mul_comp [MulOneClass M] [MulOneClass N] [CommMonoid P] (g₁ g₂ : N →* P) (f : M →* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
#align monoid_hom.mul_comp MonoidHom.mul_comp
#align add_monoid_hom.add_comp AddMonoidHom.add_comp

@[to_additive]
theorem comp_mul [MulOneClass M] [CommMonoid N] [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]
#align monoid_hom.comp_mul MonoidHom.comp_mul
#align add_monoid_hom.comp_add AddMonoidHom.comp_add

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`.  -/
@[to_additive
  "A homomorphism from an additive group to an additive monoid is injective iff
  its kernel is trivial. For the iff statement on the triviality of the kernel,
  see `injective_iff_map_eq_zero'`."]
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [NDFunLike F G H] [MonoidHomClass F G H]
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
    [NDFunLike F G H] [MonoidHomClass F G H]
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

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive "If `f` is an additive monoid homomorphism to an additive commutative group,
then `-f` is the homomorphism sending `x` to `-(f x)`."]
instance {M G} [MulOneClass M] [CommGroup G] : Inv (M →* G) :=
  ⟨fun f => (mk' fun g => (f g)⁻¹) fun a b => by rw [← mul_inv, f.map_mul]⟩

@[to_additive (attr := simp)]
theorem inv_apply {M G} [MulOneClass M] [CommGroup G] (f : M →* G) (x : M) :
    f⁻¹ x = (f x)⁻¹ := rfl
#align monoid_hom.inv_apply MonoidHom.inv_apply
#align add_monoid_hom.neg_apply AddMonoidHom.neg_apply

@[to_additive (attr := simp)]
theorem inv_comp {M N A} [MulOneClass M] [MulOneClass N] [CommGroup A]
    (φ : N →* A) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, coe_comp]
#align monoid_hom.inv_comp MonoidHom.inv_comp
#align add_monoid_hom.neg_comp AddMonoidHom.neg_comp

@[to_additive (attr := simp)]
theorem comp_inv {M A B} [MulOneClass M] [CommGroup A] [CommGroup B]
    (φ : A →* B) (ψ : M →* A) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, map_inv, coe_comp]
#align monoid_hom.comp_inv MonoidHom.comp_inv
#align add_monoid_hom.comp_neg AddMonoidHom.comp_neg

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive "If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`."]
instance {M G} [MulOneClass M] [CommGroup G] : Div (M →* G) :=
  ⟨fun f g => (mk' fun x => f x / g x) fun a b => by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]⟩

@[to_additive (attr := simp)]
theorem div_apply {M G} [MulOneClass M] [CommGroup G] (f g : M →* G) (x : M) :
    (f / g) x = f x / g x := rfl
#align monoid_hom.div_apply MonoidHom.div_apply
#align add_monoid_hom.sub_apply AddMonoidHom.sub_apply

end MonoidHom

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid
with zero morphism sending `x` to `f x * g x`. -/
instance [MulZeroOneClass M] [CommMonoidWithZero N] : Mul (M →*₀ N) :=
  ⟨fun f g => { (f * g : M →* N) with
    toFun := fun a => f a * g a,
    map_zero' := by dsimp only []; rw [map_zero, zero_mul] }⟩
    -- Porting note: why do we need `dsimp` here?
