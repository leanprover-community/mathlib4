/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.FunLike

/-!
# Additional lemmas about monoid and group homomorphisms

-/

@[expose] public section

-- `NeZero` cannot be additivised, hence its theory should be developed outside of the
-- `Algebra.Group` folder.
assert_not_imported Mathlib.Algebra.NeZero

variable {α M N P : Type*}

section One

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the homomorphism sending all elements to `0`. -/]
instance [One M] [One N] : One (OneHom M N) := ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive homomorphism sending all elements to `0` -/]
instance [Mul M] [MulOneClass N] : One (M →ₙ* N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the additive monoid homomorphism sending all elements to `0`. -/]
instance [MulOne M] [MulOneClass N] : One (M →* N) :=
  ⟨⟨⟨fun _ => 1, rfl⟩, fun _ _ => (one_mul 1).symm⟩⟩

instance AddMonoid.End.instZero [AddZeroClass M] : Zero (AddMonoid.End M) := instZeroAddMonoidHom

@[to_additive]
instance OneHom.instFunLikeOne [One M] [One N] : FunLikeOne (OneHom M N) M N where
  one_apply _ := rfl

--@[to_additive (attr := simp)]
--theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 := rfl

@[to_additive]
instance MonoidHom.instFunLikeOne [MulOne M] [MulOneClass N] : FunLikeOne (M →* N) M N where
  one_apply _ := rfl

instance AddMonoid.End.instFunLikeZero [AddZeroClass M] :
    FunLikeZero (AddMonoid.End M) M M where
  zero_apply _ := rfl

--@[to_additive (attr := simp)]
--theorem MonoidHom.one_apply [MulOne M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 := rfl

@[to_additive (attr := simp)]
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) :
    (1 : OneHom N P).comp f = 1 := rfl

@[to_additive (attr := simp)]
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp

@[to_additive]
instance [One M] [One N] : Inhabited (OneHom M N) := ⟨1⟩

@[to_additive]
instance [Mul M] [MulOneClass N] : Inhabited (M →ₙ* N) := ⟨1⟩

@[to_additive]
instance [MulOne M] [MulOneClass N] : Inhabited (M →* N) := ⟨1⟩

namespace MonoidHom

@[to_additive (attr := simp)]
theorem one_comp [MulOne M] [MulOne N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 := rfl

@[to_additive (attr := simp)]
theorem comp_one [MulOne M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp

end MonoidHom

end One

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

section CommMonoid
variable [CommMonoid α]

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps) /-- Multiplication by a natural `n` on a commutative additive monoid,
considered as a morphism of additive monoids. -/]
def powMonoidHom (n : ℕ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n

end CommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps) /-- Multiplication by an integer `n` on a commutative additive group,
considered as an additive group homomorphism. -/]
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive /-- Negation on a commutative additive group, considered as an additive monoid
homomorphism. -/]
def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[to_additive (attr := simp)]
theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv := rfl

@[to_additive (attr := simp)]
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl

@[to_additive (attr := simp)]
theorem invMonoidHom_comp_invMonoidHom : (invMonoidHom (α := α)).comp invMonoidHom = .id _ := by
  ext; simp

end DivisionCommMonoid

namespace OneHom

/-- Given two one-preserving morphisms `f`, `g`,
`f * g` is the one-preserving morphism sending `x` to `f x * g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f + g` is the zero-preserving morphism sending `x` to `f x + g x`. -/]
instance [One M] [MulOneClass N] : Mul (OneHom M N) where
  mul f g :=
    { toFun m := f m * g m
      map_one' := by simp}

@[to_additive]
instance instFunLikeMul [One M] [MulOneClass N] : FunLikeMul (OneHom M N) M N where
  mul_apply _ _ _ := rfl

@[deprecated (since := "2026-01-02")]
alias coe_mul := FunLike.coe_mul

@[deprecated (since := "2026-01-02")]
alias mul_apply := FunLikeMul.mul_apply

/-@[to_additive (attr := norm_cast)]
theorem coe_mul {M N} [One M] [MulOneClass N] (f g : OneHom M N) : ⇑(f * g) = ⇑f * ⇑g := rfl

@[to_additive (attr := simp)]
theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
    (f * g) x = f x * g x := rfl-/

@[to_additive]
theorem mul_comp [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

/-- Given a one-preserving morphism `f`,
`f⁻¹` is the one-preserving morphism sending `x` to `(f x)⁻¹`. -/
@[to_additive /-- Given a zero-preserving morphism `f`,
`-f` is the zero-preserving morphism sending `x` to `-f x`. -/]
instance [One M] [InvOneClass N] : Inv (OneHom M N) where
  inv f :=
    { toFun m := (f m)⁻¹
      map_one' := by simp}

@[to_additive]
instance instFunLikeInv [One M] [InvOneClass N] : FunLikeInv (OneHom M N) M N where
  inv_apply _ _ := rfl

@[deprecated (since := "2026-01-02")]
alias coe_inv := FunLike.coe_inv

@[deprecated (since := "2026-01-02")]
alias inv_apply := FunLikeInv.inv_apply

/-@[to_additive (attr := norm_cast)]
theorem coe_inv {M N} [One M] [InvOneClass N] (f : OneHom M N) : ⇑(f⁻¹) = (⇑f)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem inv_apply {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M) :
    f⁻¹ x = (f x)⁻¹ := rfl-/

@[to_additive]
theorem inv_comp [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N) :
    (g⁻¹).comp f = (g.comp f)⁻¹ := rfl

/-- Given two one-preserving morphisms `f`, `g`,
`f / g` is the one-preserving morphism sending `x` to `f x / g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f - g` is the additive morphism sending `x` to `f x - g x`. -/]
instance [One M] [DivisionMonoid N] : Div (OneHom M N) where
  div f g :=
    { toFun m := f m / g m
      map_one' := by simp }

@[to_additive]
instance instFunLikeDiv [One M] [DivisionMonoid N] : FunLikeDiv (OneHom M N) M N where
  div_apply _ _ _ := rfl

@[deprecated (since := "2026-01-02")]
alias coe_div := FunLike.coe_div

@[deprecated (since := "2026-01-02")]
alias div_apply := FunLikeDiv.div_apply

/-@[to_additive (attr := norm_cast)]
theorem coe_div {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) : ⇑(f / g) = ⇑f / ⇑g := rfl

@[to_additive (attr := simp)]
theorem div_apply {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M) :
    (f / g) x = f x / g x := rfl-/

@[to_additive]
theorem div_comp [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ / g₂).comp f = g₁.comp f / g₂.comp f := rfl

end OneHom

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive /-- Given two additive morphisms `f`, `g` to an additive commutative semigroup,
`f + g` is the additive morphism sending `x` to `f x + g x`. -/]
instance [Mul M] [CommSemigroup N] : Mul (M →ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

@[to_additive]
instance instFunLikeMul [Mul M] [CommSemigroup N] : FunLikeMul (M →ₙ* N) M N where
  mul_apply _ _ _ := rfl

@[deprecated (since := "2026-01-02")]
alias coe_mul := FunLike.coe_mul

@[deprecated (since := "2026-01-02")]
alias mul_apply := FunLikeMul.mul_apply

/-@[to_additive (attr := simp)]
theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl-/

@[to_additive]
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp

end MulHom

namespace MonoidHom
section Group
variable [Group G]

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`. -/
@[to_additive
  /-- A homomorphism from an additive group to an additive monoid is injective iff
  its kernel is trivial. For the iff statement on the triviality of the kernel,
  see `injective_iff_map_eq_zero'`. -/]
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
  /-- A homomorphism from an additive group to an additive monoid is injective iff its
  kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
  `injective_iff_map_eq_zero`. -/]
theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  (injective_iff_map_eq_one f).trans <|
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

/-- Makes a group homomorphism from a proof that the map preserves right division
`fun x y => x * y⁻¹`. See also `MonoidHom.of_map_div` for a version using `fun x y => x / y`.
-/
@[to_additive
  /-- Makes an additive group homomorphism from a proof that the map preserves
  the operation `fun a b => a + -b`. See also `AddMonoidHom.ofMapSub` for a version using
  `fun a b => a - b`. -/]
def ofMapMulInv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]
theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ↑(ofMapMulInv f map_div) = f :=
  rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive /-- Define a morphism of additive groups given a map which respects difference. -/]
def ofMapDiv {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]
theorem coe_of_map_div {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ↑(ofMapDiv f hf) = f := rfl

end Group

section Mul
variable [MulOneClass M] [CommMonoid N]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance instMul : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.instAdd

@[deprecated (since := "2026-01-02")]
alias _root_.AddMonoidHom.add := AddMonoidHom.instAdd

@[deprecated (since := "2026-01-02")]
alias mul := MonoidHom.instMul

@[to_additive]
instance instFunLikeMul : FunLikeMul (M →* N) M N where
  mul_apply _ _ _ := rfl

--@[to_additive (attr := simp)]
--lemma mul_apply (f g : M →* N) (x : M) : (f * g) x = f x * g x := rfl

@[to_additive]
lemma mul_comp [MulOneClass P] (g₁ g₂ : M →* N) (f : P →* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
lemma comp_mul [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext; simp

end Mul

section InvDiv
variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism to an additive commutative group,
then `-f` is the homomorphism sending `x` to `-(f x)`. -/]
instance : Inv (M →* G) where
  inv f := mk' (fun g ↦ (f g)⁻¹) fun a b ↦ by simp_rw [← mul_inv, f.map_mul]

@[to_additive]
instance instFunLikeInv : FunLikeInv (M →* G) M G where
  inv_apply _ _ := rfl

--@[to_additive (attr := simp)] lemma inv_apply (f : M →* G) (x : M) : f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem inv_comp (φ : N →* G) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem comp_inv (φ : G →* H) (ψ : M →* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext; simp

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive /-- If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`. -/]
instance : Div (M →* G) where
  div f g := mk' (fun x ↦ f x / g x) fun a b ↦ by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

@[to_additive]
instance instFunLikeDiv : FunLikeDiv (M →* G) M G where
  div_apply _ _ _ := rfl

--@[to_additive (attr := simp)]
--lemma div_apply (f g : M →* G) (x : M) : (f / g) x = f x / g x := rfl

@[to_additive (attr := simp)]
lemma div_comp (f g : N →* G) (h : M →* N) : (f / g).comp h = f.comp h / g.comp h := rfl

@[to_additive (attr := simp)]
lemma comp_div (f : G →* H) (g h : M →* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext; simp

end InvDiv

/-- If `H` is commutative and `G →* H` is injective, then `G` is commutative. -/
def commGroupOfInjective [Group G] [CommGroup H] (f : G →* H) (hf : Function.Injective f) :
    CommGroup G :=
  ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

/-- If `G` is commutative and `G →* H` is surjective, then `H` is commutative. -/
def commGroupOfSurjective [CommGroup G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    CommGroup H :=
  ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

end MonoidHom

namespace AddMonoid.End

instance instAdd [AddCommMonoid M] : Add (AddMonoid.End M) :=
  AddMonoidHom.instAdd

instance instFunLikeAdd [AddCommMonoid M] : FunLikeAdd (AddMonoid.End M) M M :=
  AddMonoidHom.instFunLikeAdd

instance instNeg [AddCommGroup M] : Neg (AddMonoid.End M) :=
  AddMonoidHom.instNeg

instance instFunLikeNeg [AddCommGroup M] : FunLikeNeg (AddMonoid.End M) M M :=
  AddMonoidHom.instFunLikeNeg

instance instSub [AddCommGroup M] : Sub (AddMonoid.End M) :=
  AddMonoidHom.instSub

instance instFunLikeSub [AddCommGroup M] : FunLikeSub (AddMonoid.End M) M M :=
  AddMonoidHom.instFunLikeSub

end AddMonoid.End
