/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Ring.Basic

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


universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

/-- `(M →* N)` is a `CommMonoid` if `N` is commutative. -/
@[to_additive "`(M →+ N)` is an `AddCommMonoid` if `N` is commutative."]
instance MonoidHom.commMonoid [MulOneClass M] [CommMonoid N] :
    CommMonoid (M →* N) where
  mul := (· * ·)
  mul_assoc := by intros; ext; apply mul_assoc
                  -- ⊢ a✝ * b✝ * c✝ = a✝ * (b✝ * c✝)
                          -- ⊢ ↑(a✝ * b✝ * c✝) x✝ = ↑(a✝ * (b✝ * c✝)) x✝
                               -- 🎉 no goals
  one := 1
  one_mul := by intros; ext; apply one_mul
                -- ⊢ 1 * a✝ = a✝
                        -- ⊢ ↑(1 * a✝) x✝ = ↑a✝ x✝
                             -- 🎉 no goals
  mul_one := by intros; ext; apply mul_one
                -- ⊢ a✝ * 1 = a✝
                        -- ⊢ ↑(a✝ * 1) x✝ = ↑a✝ x✝
                             -- 🎉 no goals
  mul_comm := by intros; ext; apply mul_comm
                 -- ⊢ a✝ * b✝ = b✝ * a✝
                         -- ⊢ ↑(a✝ * b✝) x✝ = ↑(b✝ * a✝) x✝
                                                -- 🎉 no goals
                                                                                -- 🎉 no goals
                              -- 🎉 no goals
  npow n f :=
    -- ⊢ ↑((fun n f => { toOneHom := { toFun := fun x => ↑f x ^ n, map_one' := (_ : ↑ …
    { toFun := fun x => f x ^ n, map_one' := by simp, map_mul' := fun x y => by simp [mul_pow] }
    -- 🎉 no goals
  npow_zero f := by
    ext x
    -- ⊢ ↑((fun n f => { toOneHom := { toFun := fun x => ↑f x ^ n, map_one' := (_ : ↑ …
    simp
    -- 🎉 no goals
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
      -- ⊢ a✝ / b✝ = a✝ * b✝⁻¹
      ext
      -- ⊢ ↑(a✝ / b✝) x✝ = ↑(a✝ * b✝⁻¹) x✝
      apply div_eq_mul_inv,
      -- 🎉 no goals
    mul_left_inv := by intros; ext; apply mul_left_inv,
                       -- ⊢ a✝⁻¹ * a✝ = 1
                               -- ⊢ ↑(a✝⁻¹ * a✝) x✝ = ↑1 x✝
                                    -- 🎉 no goals
                       -- 🎉 no goals
    zpow := fun n f =>
                                  -- 🎉 no goals
      { toFun := fun x => f x ^ n,
        map_one' := by simp,
      -- ⊢ ↑((fun n f => { toOneHom := { toFun := fun x => ↑f x ^ n, map_one' := (_ : ↑ …
        map_mul' := fun x y => by simp [mul_zpow] },
      -- 🎉 no goals
    zpow_zero' := fun f => by
      ext x
      -- ⊢ ↑((fun n f => { toOneHom := { toFun := fun x => ↑f x ^ n, map_one' := (_ : ↑ …
      simp,
      -- 🎉 no goals
    zpow_succ' := fun n f => by
      ext x
      -- ⊢ ↑((fun n f => { toOneHom := { toFun := fun x => ↑f x ^ n, map_one' := (_ : ↑ …
      simp [zpow_ofNat, pow_succ],
      -- 🎉 no goals
    zpow_neg' := fun n f => by
      ext x
      simp [Nat.succ_eq_add_one, zpow_ofNat] }

instance [AddCommMonoid M] : AddCommMonoid (AddMonoid.End M) :=
  AddMonoidHom.addCommMonoid

instance AddMonoid.End.semiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  { AddMonoid.End.monoid M, AddMonoidHom.addCommMonoid with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl,
    natCast := fun n => n • (1 : AddMonoid.End M),
    natCast_zero := AddMonoid.nsmul_zero _,
    natCast_succ := fun n => (AddMonoid.nsmul_succ n 1).trans (add_comm _ _) }

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
theorem AddMonoid.End.natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) :
    (↑n : AddMonoid.End M) m = n • m :=
  rfl
#align add_monoid.End.nat_cast_apply AddMonoid.End.natCast_apply

instance [AddCommGroup M] : AddCommGroup (AddMonoid.End M) :=
  AddMonoidHom.addCommGroup

instance [AddCommGroup M] : Ring (AddMonoid.End M) :=
  { AddMonoid.End.semiring, AddMonoidHom.addCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := ofNat_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

/-- See also `AddMonoid.End.intCast_def`. -/
@[simp]
theorem AddMonoid.End.int_cast_apply [AddCommGroup M] (z : ℤ) (m : M) :
    (↑z : AddMonoid.End M) m = z • m :=
  rfl
#align add_monoid.End.int_cast_apply AddMonoid.End.int_cast_apply

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/


namespace MonoidHom

@[to_additive]
theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y :=
  FunLike.ext_iff.trans <| forall_congr' fun _ => FunLike.ext_iff
#align monoid_hom.ext_iff₂ MonoidHom.ext_iff₂
#align add_monoid_hom.ext_iff₂ AddMonoidHom.ext_iff₂

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive "`flip` arguments of `f : M →+ N →+ P`"]
def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M →* N →* P) :
    N →* M →* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
                     -- 🎉 no goals
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
                                  -- 🎉 no goals
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
    -- ⊢ ↑((fun g => { toOneHom := { toFun := comp g, map_one' := (_ : comp g 1 = 1)  …
    exact one_comp f
    -- 🎉 no goals
  map_mul' g₁ g₂ := by
    ext1 f
    -- ⊢ ↑(OneHom.toFun { toFun := fun g => { toOneHom := { toFun := comp g, map_one' …
    exact mul_comp g₁ g₂ f
    -- 🎉 no goals
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

/-!
### Miscellaneous definitions

Due to the fact this file imports `Algebra.GroupPower.Basic`, it is not possible to import it in
some of the lower-level files like `Algebra.Ring.Basic`. The following lemmas should be rehomed
if the import structure permits them to be.
-/


section Semiring

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both arguments.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoidHom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgHom.mul`
and `Algebra.lmul`.
-/
def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' a b := AddMonoidHom.ext <| add_mul a b
#align add_monoid_hom.mul AddMonoidHom.mul

theorem AddMonoidHom.mul_apply (x y : R) : AddMonoidHom.mul x y = x * y :=
  rfl
#align add_monoid_hom.mul_apply AddMonoidHom.mul_apply

@[simp]
theorem AddMonoidHom.coe_mul : ⇑(AddMonoidHom.mul : R →+ R →+ R) = AddMonoidHom.mulLeft :=
  rfl
#align add_monoid_hom.coe_mul AddMonoidHom.coe_mul

@[simp]
theorem AddMonoidHom.coe_flip_mul :
    ⇑(AddMonoidHom.mul : R →+ R →+ R).flip = AddMonoidHom.mulRight :=
  rfl
#align add_monoid_hom.coe_flip_mul AddMonoidHom.coe_flip_mul

/-- An `AddMonoidHom` preserves multiplication if pre- and post- composition with
`AddMonoidHom.mul` are equivalent. By converting the statement into an equality of
`AddMonoidHom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
theorem AddMonoidHom.map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (AddMonoidHom.mul : R →+ R →+ R).compr₂ f = (AddMonoidHom.mul.comp f).compl₂ f :=
  Iff.symm AddMonoidHom.ext_iff₂
#align add_monoid_hom.map_mul_iff AddMonoidHom.map_mul_iff

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`. -/
@[simps!]
def AddMonoid.End.mulLeft : R →+ AddMonoid.End R :=
  AddMonoidHom.mul
#align add_monoid.End.mul_left AddMonoid.End.mulLeft
#align add_monoid.End.mul_left_apply_apply AddMonoid.End.mulLeft_apply_apply

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`. -/
@[simps!]
def AddMonoid.End.mulRight : R →+ AddMonoid.End R :=
  (AddMonoidHom.mul : R →+ AddMonoid.End R).flip
#align add_monoid.End.mul_right AddMonoid.End.mulRight
#align add_monoid.End.mul_right_apply_apply AddMonoid.End.mulRight_apply_apply

end Semiring
