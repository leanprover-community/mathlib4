/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Instances on spaces of monoid and group morphisms

We endow the space of monoid morphisms `M →* N` with a `Monoid` structure and an
`IsMulCommutative` instance when the target is commutative, through pointwise multiplication, and
with a `Group` structure when the target is a commutative group. We also prove the same instances
for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `Ring` structure on `AddMonoid.End`.
-/

@[expose] public section

assert_not_exists AddMonoidWithOne Ring

universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

@[to_additive]
instance OneHom.instPow [One M] [Monoid N] : Pow (OneHom M N) ℕ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
instance MonoidHom.instPow [MulOneClass M] [Monoid N] [IsMulCommutative N] : Pow (M →* N) ℕ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[to_additive (attr := simp)]
lemma OneHom.pow_apply [One M] [Monoid N] (f : OneHom M N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

@[to_additive (attr := simp)]
lemma MonoidHom.pow_apply [MulOneClass M] [Monoid N] [IsMulCommutative N] (f : M →* N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

/-- `OneHom M N` is a `Monoid` if `N` is. -/
@[to_additive /-- `ZeroHom M N` is an `AddMonoid` if `N` is. -/]
instance OneHom.instMonoid [One M] [Monoid N] : Monoid (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `OneHom M N` is commutative if `N` is commutative. -/
@[to_additive /-- `ZeroHom M N` is commutative if `N` is commutative. -/]
instance OneHom.instIsMulCommutative [One M] [MulOneClass N] [IsMulCommutative N] :
    IsMulCommutative (OneHom M N) :=
  DFunLike.coe_injective.isMulCommutative DFunLike.coe (fun _ _ => rfl)

/-- `(M →* N)` is a `Monoid` if `N` is a commutative monoid. -/
@[to_additive /-- `(M →+ N)` is an `AddMonoid` if `N` is an additive commutative monoid. -/]
instance MonoidHom.instMonoid [MulOneClass M] [Monoid N] [IsMulCommutative N] : Monoid (M →* N) :=
  fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `(M →* N)` is commutative if `N` is a commutative monoid. -/
@[to_additive /-- `(M →+ N)` is commutative if `N` is an additive commutative monoid. -/]
instance MonoidHom.instIsMulCommutative [MulOneClass M] [Monoid N] [IsMulCommutative N] :
    IsMulCommutative (M →* N) :=
  DFunLike.coe_injective.isMulCommutative DFunLike.coe (fun _ _ => rfl)

@[to_additive]
instance OneHom.instZPow [One M] [Group N] : Pow (OneHom M N) ℤ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
instance MonoidHom.instZPow [MulOneClass M] [Group N] [IsMulCommutative N] : Pow (M →* N) ℤ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_zpow] }

@[to_additive (attr := simp)]
lemma OneHom.zpow_apply [One M] [Group N] (f : OneHom M N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

@[to_additive (attr := simp)]
lemma MonoidHom.zpow_apply [MulOneClass M] [Group N] [IsMulCommutative N] (f : M →* N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

/-- If `G` is a group, then so is `OneHom M G`. -/
@[to_additive /-- If `G` is an additive group, then so is `ZeroHom M G`. -/]
instance OneHom.instGroup [One M] [Group N] : Group (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- If `G` is a commutative group, then `M →* G` is a group too. -/
@[to_additive /-- If `G` is an additive commutative group, then `M →+ G` is an additive
      group too. -/]
instance MonoidHom.instGroup [MulOneClass M] [Group N] [IsMulCommutative N] : Group (M →* N) :=
  fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [One M] [MulOneClass N] [IsLeftCancelMul N] : IsLeftCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
instance [MulOneClass M] [Monoid N] [IsMulCommutative N] [IsLeftCancelMul N] : IsLeftCancelMul (M →* N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
instance [One M] [MulOneClass N] [IsRightCancelMul N] : IsRightCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
instance [MulOneClass M] [Monoid N] [IsMulCommutative N] [IsRightCancelMul N] : IsRightCancelMul (M →* N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
instance [One M] [MulOneClass N] [IsCancelMul N] : IsCancelMul (OneHom M N) where

@[to_additive]
instance [MulOneClass M] [Monoid N] [IsMulCommutative N] [IsCancelMul N] : IsCancelMul (M →* N) where

section End

instance AddMonoid.End.instAddMonoid [AddMonoid M] [IsAddCommutative M] :
    AddMonoid (AddMonoid.End M) :=
  inferInstanceAs <| AddMonoid (M →+ M)

instance AddMonoid.End.instIsAddCommutative [AddMonoid M] [IsAddCommutative M] :
    IsAddCommutative (AddMonoid.End M) :=
  inferInstanceAs <| IsAddCommutative (M →+ M)

@[simp]
theorem AddMonoid.End.zero_apply [AddMonoid M] [IsAddCommutative M] (m : M) : (0 : AddMonoid.End M) m = 0 :=
  rfl

-- Note: `@[simp]` omitted because `(1 : AddMonoid.End M) = id` by `AddMonoid.End.coe_one`
theorem AddMonoid.End.one_apply [AddZeroClass M] (m : M) : (1 : AddMonoid.End M) m = m :=
  rfl

instance AddMonoid.End.instAddGroup [AddGroup M] [IsAddCommutative M] :
    AddGroup (AddMonoid.End M) :=
  inferInstanceAs <| AddGroup (M →+ M)

instance AddMonoid.End.instIntCast [AddGroup M] [IsAddCommutative M] : IntCast (AddMonoid.End M) where
  intCast := fun z => z • 1

/-- See also `AddMonoid.End.intCast_def`. -/
@[simp]
theorem AddMonoid.End.intCast_apply [AddGroup M] [IsAddCommutative M] (z : ℤ) (m : M) :
    (↑z : AddMonoid.End M) m = z • m :=
  rfl

end End

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/


namespace MonoidHom

@[to_additive]
theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : Monoid P} [IsMulCommutative P] {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y :=
  DFunLike.ext_iff.trans <| forall_congr' fun _ => DFunLike.ext_iff

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive /-- `flip` arguments of `f : M →+ N →+ P` -/]
def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : Monoid P} [IsMulCommutative P] (f : M →* N →* P) :
    N →* M →* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂

@[to_additive (attr := simp)]
theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : Monoid P} [IsMulCommutative P] (f : M →* N →* P)
    (x : M) (y : N) : f.flip y x = f x y :=
  rfl

@[to_additive]
theorem map_one₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : Monoid P} [IsMulCommutative P] (f : M →* N →* P)
    (n : N) : f 1 n = 1 :=
  (flip f n).map_one

@[to_additive]
theorem map_mul₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : Monoid P} [IsMulCommutative P] (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
  (flip f n).map_mul _ _

@[to_additive]
theorem map_inv₂ {_ : Group M} {_ : MulOneClass N} {_ : Group P} [IsMulCommutative P] (f : M →* N →* P) (m : M)
    (n : N) : f m⁻¹ n = (f m n)⁻¹ :=
  (flip f n).map_inv _

@[to_additive]
theorem map_div₂ {_ : Group M} {_ : MulOneClass N} {_ : Group P} [IsMulCommutative P] (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n :=
  (flip f n).map_div _ _

/-- Evaluation of a `MonoidHom` at a point as a monoid homomorphism. See also `MonoidHom.apply`
for the evaluation of any function at a point. -/
@[to_additive (attr := simps!)
      /-- Evaluation of an `AddMonoidHom` at a point as an additive monoid homomorphism.
      See also `AddMonoidHom.apply` for the evaluation of any function at a point. -/]
def eval [MulOneClass M] [Monoid N] [IsMulCommutative N] : M →* (M →* N) →* N :=
  (MonoidHom.id (M →* N)).flip

/-- The expression `fun g m ↦ g (f m)` as a `MonoidHom`.
Equivalently, `(fun g ↦ MonoidHom.comp g f)` as a `MonoidHom`. -/
@[to_additive (attr := simps!)
      /-- The expression `fun g m ↦ g (f m)` as an `AddMonoidHom`.
      Equivalently, `(fun g ↦ AddMonoidHom.comp g f)` as an `AddMonoidHom`.

      This also exists in a `LinearMap` version, `LinearMap.lcomp`. -/]
def compHom' [MulOneClass M] [MulOneClass N] [Monoid P] [IsMulCommutative P] (f : M →* N) : (N →* P) →* M →* P :=
  flip <| eval.comp f

/-- Composition of monoid morphisms (`MonoidHom.comp`) as a monoid morphism.

Note that unlike `MonoidHom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive (attr := simps)
      /-- Composition of additive monoid morphisms (`AddMonoidHom.comp`) as an additive
      monoid morphism.

      Note that unlike `AddMonoidHom.comp_hom'` this requires commutativity of `N`.

      This also exists in a `LinearMap` version, `LinearMap.llcomp`. -/]
def compHom [MulOneClass M] [Monoid N] [IsMulCommutative N] [Monoid P] [IsMulCommutative P] :
    (N →* P) →* (M →* N) →* M →* P where
  toFun g := { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f

/-- Flipping arguments of monoid morphisms (`MonoidHom.flip`) as a monoid morphism. -/
@[to_additive (attr := simps)
      /-- Flipping arguments of additive monoid morphisms (`AddMonoidHom.flip`)
      as an additive monoid morphism. -/]
def flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : Monoid P} [IsMulCommutative P] :
    (M →* N →* P) →* N →* M →* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The expression `fun m q ↦ f m (g q)` as a `MonoidHom`.

Note that the expression `fun q n ↦ f (g q) n` is simply `MonoidHom.comp`. -/
@[to_additive
      /-- The expression `fun m q ↦ f m (g q)` as an `AddMonoidHom`.

      Note that the expression `fun q n ↦ f (g q) n` is simply `AddMonoidHom.comp`.

      This also exists as a `LinearMap` version, `LinearMap.compl₂` -/]
def compl₂ [MulOneClass M] [MulOneClass N] [Monoid P] [IsMulCommutative P] [MulOneClass Q] (f : M →* N →* P)
    (g : Q →* N) : M →* Q →* P :=
  (compHom' g).comp f

@[to_additive (attr := simp)]
theorem compl₂_apply [MulOneClass M] [MulOneClass N] [Monoid P] [IsMulCommutative P] [MulOneClass Q]
    (f : M →* N →* P) (g : Q →* N) (m : M) (q : Q) : (compl₂ f g) m q = f m (g q) :=
  rfl

/-- The expression `fun m n ↦ g (f m n)` as a `MonoidHom`. -/
@[to_additive
      /-- The expression `fun m n ↦ g (f m n)` as an `AddMonoidHom`.

      This also exists as a `LinearMap` version, `LinearMap.compr₂` -/]
def compr₂ [MulOneClass M] [MulOneClass N] [Monoid P] [IsMulCommutative P] [Monoid Q] [IsMulCommutative Q] (f : M →* N →* P)
    (g : P →* Q) : M →* N →* Q :=
  (compHom g).comp f

@[to_additive (attr := simp)]
theorem compr₂_apply [MulOneClass M] [MulOneClass N] [Monoid P] [IsMulCommutative P] [Monoid Q] [IsMulCommutative Q] (f : M →* N →* P)
    (g : P →* Q) (m : M) (n : N) : (compr₂ f g) m n = g (f m n) :=
  rfl

end MonoidHom
