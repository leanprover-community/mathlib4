/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Hom.Basic

#align_import algebra.hom.group_instances from "leanprover-community/mathlib"@"2ed7e4aec72395b6a7c3ac4ac7873a7a43ead17c"

/-!
# Instances on spaces of monoid and group morphisms

We endow the space of monoid morphisms `M →* N` with a `CommMonoid` structure when the target is
commutative, through pointwise multiplication, and with a `CommGroup` structure when the target
is a commutative group. We also prove the same instances for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `Ring` structure on `AddMonoid.End`.
-/

assert_not_exists AddMonoidWithOne

universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

/-- `(M →* N)` is a `CommMonoid` if `N` is commutative. -/
@[to_additive "`(M →+ N)` is an `AddCommMonoid` if `N` is commutative."]
instance MonoidHom.commMonoid [MulOneClass M] [CommMonoid N] :
    CommMonoid (M →* N) where
  mul := (· * ·)
  mul_assoc := by intros; ext; apply mul_assoc
  one := 1
  one_mul := by intros; ext; apply one_mul
  mul_one := by intros; ext; apply mul_one
  mul_comm := by intros; ext; apply mul_comm
  npow n f :=
    { toFun := fun x => f x ^ n, map_one' := by simp, map_mul' := fun x y => by simp [mul_pow] }
  npow_zero f := by
    ext x
    simp
  npow_succ n f := by
    ext x
    simp [pow_succ]

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive "If `G` is an additive commutative group, then `M →+ G` is an additive commutative
      group too."]
instance MonoidHom.commGroup {M G} [MulOneClass M] [CommGroup G] : CommGroup (M →* G) :=
  { MonoidHom.commMonoid with
    inv := Inv.inv,
    div := Div.div,
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv,
    mul_left_inv := by intros; ext; apply mul_left_inv,
    zpow := fun n f =>
      { toFun := fun x => f x ^ n,
        map_one' := by simp,
        map_mul' := fun x y => by simp [mul_zpow] },
    zpow_zero' := fun f => by
      ext x
      simp,
    zpow_succ' := fun n f => by
      ext x
      -- Adaptation note: nightly-2024-03-24
      -- We used to need a `simp [mul_comm]` after `simp [zpow_add_one]`.
      -- Writing `simp [zpow_add_one, mul_comm]` still shows the bug mentioned below.
      -- Adaptation note: nightly-2024-03-13
      -- https://github.com/leanprover-community/mathlib4/issues/11357
      -- If we add `mul_comm` to the simp call we reveal a bug: "unexpected bound variable #0"
      -- Hopefully we can minimize this.
      simp [zpow_add_one],
    zpow_neg' := fun n f => by
      ext x
      simp [Nat.succ_eq_add_one, zpow_natCast, -Int.natCast_add] }

instance AddMonoid.End.instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (AddMonoid.End M) :=
  AddMonoidHom.addCommMonoid

@[simp]
theorem AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M) m = 0 :=
  rfl

-- Note: `@[simp]` omitted because `(1 : AddMonoid.End M) = id` by `AddMonoid.coe_one`
theorem AddMonoid.End.one_apply [AddCommMonoid M] (m : M) : (1 : AddMonoid.End M) m = m :=
  rfl

instance AddMonoid.End.instAddCommGroup [AddCommGroup M] : AddCommGroup (AddMonoid.End M) :=
  AddMonoidHom.addCommGroup

instance AddMonoid.End.instIntCast [AddCommGroup M] : IntCast (AddMonoid.End M) :=
  { intCast := fun z => z • (1 : AddMonoid.End M) }

/-- See also `AddMonoid.End.intCast_def`. -/
@[simp]
theorem AddMonoid.End.intCast_apply [AddCommGroup M] (z : ℤ) (m : M) :
    (↑z : AddMonoid.End M) m = z • m :=
  rfl
#align add_monoid.End.int_cast_apply AddMonoid.End.intCast_apply

@[deprecated (since := "2024-04-17")]
alias AddMonoid.End.int_cast_apply := AddMonoid.End.intCast_apply

@[to_additive (attr := simp)] lemma MonoidHom.pow_apply {M N : Type*} [MulOneClass M]
    [CommMonoid N] (f : M →* N) (n : ℕ) (x : M) :
    (f ^ n) x = (f x) ^ n :=
  rfl

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/


namespace MonoidHom

@[to_additive]
theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y :=
  DFunLike.ext_iff.trans <| forall_congr' fun _ => DFunLike.ext_iff
#align monoid_hom.ext_iff₂ MonoidHom.ext_iff₂
#align add_monoid_hom.ext_iff₂ AddMonoidHom.ext_iff₂

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive "`flip` arguments of `f : M →+ N →+ P`"]
def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M →* N →* P) :
    N →* M →* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂
#align monoid_hom.flip MonoidHom.flip
#align add_monoid_hom.flip AddMonoidHom.flip

@[to_additive (attr := simp)]
theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (x : M) (y : N) : f.flip y x = f x y :=
  rfl
#align monoid_hom.flip_apply MonoidHom.flip_apply
#align add_monoid_hom.flip_apply AddMonoidHom.flip_apply

@[to_additive]
theorem map_one₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (n : N) : f 1 n = 1 :=
  (flip f n).map_one
#align monoid_hom.map_one₂ MonoidHom.map_one₂
#align add_monoid_hom.map_one₂ AddMonoidHom.map_one₂

@[to_additive]
theorem map_mul₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
  (flip f n).map_mul _ _
#align monoid_hom.map_mul₂ MonoidHom.map_mul₂
#align add_monoid_hom.map_mul₂ AddMonoidHom.map_mul₂

@[to_additive]
theorem map_inv₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P) (m : M)
    (n : N) : f m⁻¹ n = (f m n)⁻¹ :=
  (flip f n).map_inv _
#align monoid_hom.map_inv₂ MonoidHom.map_inv₂
#align add_monoid_hom.map_inv₂ AddMonoidHom.map_inv₂

@[to_additive]
theorem map_div₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n :=
  (flip f n).map_div _ _
#align monoid_hom.map_div₂ MonoidHom.map_div₂
#align add_monoid_hom.map_div₂ AddMonoidHom.map_div₂

/-- Evaluation of a `MonoidHom` at a point as a monoid homomorphism. See also `MonoidHom.apply`
for the evaluation of any function at a point. -/
@[to_additive (attr := simps!)
      "Evaluation of an `AddMonoidHom` at a point as an additive monoid homomorphism.
      See also `AddMonoidHom.apply` for the evaluation of any function at a point."]
def eval [MulOneClass M] [CommMonoid N] : M →* (M →* N) →* N :=
  (MonoidHom.id (M →* N)).flip
#align monoid_hom.eval MonoidHom.eval
#align add_monoid_hom.eval AddMonoidHom.eval
#align monoid_hom.eval_apply_apply MonoidHom.eval_apply_apply
#align add_monoid_hom.eval_apply_apply AddMonoidHom.eval_apply_apply

/-- The expression `fun g m ↦ g (f m)` as a `MonoidHom`.
Equivalently, `(fun g ↦ MonoidHom.comp g f)` as a `MonoidHom`. -/
@[to_additive (attr := simps!)
      "The expression `fun g m ↦ g (f m)` as an `AddMonoidHom`.
      Equivalently, `(fun g ↦ AddMonoidHom.comp g f)` as an `AddMonoidHom`.

      This also exists in a `LinearMap` version, `LinearMap.lcomp`."]
def compHom' [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M →* N) : (N →* P) →* M →* P :=
  flip <| eval.comp f
#align monoid_hom.comp_hom' MonoidHom.compHom'
#align add_monoid_hom.comp_hom' AddMonoidHom.compHom'
#align monoid_hom.comp_hom'_apply_apply MonoidHom.compHom'_apply_apply
#align add_monoid_hom.comp_hom'_apply_apply AddMonoidHom.compHom'_apply_apply

/-- Composition of monoid morphisms (`MonoidHom.comp`) as a monoid morphism.

Note that unlike `MonoidHom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive (attr := simps)
      "Composition of additive monoid morphisms (`AddMonoidHom.comp`) as an additive
      monoid morphism.

      Note that unlike `AddMonoidHom.comp_hom'` this requires commutativity of `N`.

      This also exists in a `LinearMap` version, `LinearMap.llcomp`."]
def compHom [MulOneClass M] [CommMonoid N] [CommMonoid P] :
    (N →* P) →* (M →* N) →* M →* P where
  toFun g := { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f
#align monoid_hom.comp_hom MonoidHom.compHom
#align add_monoid_hom.comp_hom AddMonoidHom.compHom
#align monoid_hom.comp_hom_apply_apply MonoidHom.compHom_apply_apply
#align add_monoid_hom.comp_hom_apply_apply AddMonoidHom.compHom_apply_apply

/-- Flipping arguments of monoid morphisms (`MonoidHom.flip`) as a monoid morphism. -/
@[to_additive (attr := simps)
      "Flipping arguments of additive monoid morphisms (`AddMonoidHom.flip`)
      as an additive monoid morphism."]
def flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} :
    (M →* N →* P) →* N →* M →* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.flip_hom MonoidHom.flipHom
#align add_monoid_hom.flip_hom AddMonoidHom.flipHom
#align monoid_hom.flip_hom_apply MonoidHom.flipHom_apply
#align add_monoid_hom.flip_hom_apply AddMonoidHom.flipHom_apply

/-- The expression `fun m q ↦ f m (g q)` as a `MonoidHom`.

Note that the expression `fun q n ↦ f (g q) n` is simply `MonoidHom.comp`. -/
@[to_additive
      "The expression `fun m q ↦ f m (g q)` as an `AddMonoidHom`.

      Note that the expression `fun q n ↦ f (g q) n` is simply `AddMonoidHom.comp`.

      This also exists as a `LinearMap` version, `LinearMap.compl₂`"]
def compl₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q] (f : M →* N →* P)
    (g : Q →* N) : M →* Q →* P :=
  (compHom' g).comp f
#align monoid_hom.compl₂ MonoidHom.compl₂
#align add_monoid_hom.compl₂ AddMonoidHom.compl₂

@[to_additive (attr := simp)]
theorem compl₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q]
    (f : M →* N →* P) (g : Q →* N) (m : M) (q : Q) : (compl₂ f g) m q = f m (g q) :=
  rfl
#align monoid_hom.compl₂_apply MonoidHom.compl₂_apply
#align add_monoid_hom.compl₂_apply AddMonoidHom.compl₂_apply

/-- The expression `fun m n ↦ g (f m n)` as a `MonoidHom`. -/
@[to_additive
      "The expression `fun m n ↦ g (f m n)` as an `AddMonoidHom`.

      This also exists as a `LinearMap` version, `LinearMap.compr₂`"]
def compr₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) : M →* N →* Q :=
  (compHom g).comp f
#align monoid_hom.compr₂ MonoidHom.compr₂
#align add_monoid_hom.compr₂ AddMonoidHom.compr₂

@[to_additive (attr := simp)]
theorem compr₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) (m : M) (n : N) : (compr₂ f g) m n = g (f m n) :=
  rfl
#align monoid_hom.compr₂_apply MonoidHom.compr₂_apply
#align add_monoid_hom.compr₂_apply AddMonoidHom.compr₂_apply

end MonoidHom

assert_not_exists Ring
