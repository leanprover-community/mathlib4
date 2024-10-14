/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Units.Hom

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`Monoid`, `Group` etc) structures on `M × N`.
We also prove trivial `simp` lemmas, and define the following operations on `MonoidHom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `Prod.fst` and `Prod.snd`
  as `MonoidHom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g` : `M →* N × P`: sends `x` to `(f x, g x)`;
* When `P` is commutative, `f.coprod g : M × N →* P` sends `(x, y)` to `f x * g y`
  (without the commutativity assumption on `P`, see `MonoidHom.noncommPiCoprod`);
* `f.prodMap g : M × N → M' × N'`: `prod.map f g` as a `MonoidHom`,
  sends `(x, y)` to `(f x, g y)`.

## Main declarations

* `mulMulHom`/`mulMonoidHom`: Multiplication bundled as a
  multiplicative/monoid homomorphism.
* `divMonoidHom`: Division bundled as a monoid homomorphism.
-/

assert_not_exists MonoidWithZero
-- TODO:
-- assert_not_exists AddMonoidWithOne
assert_not_exists DenselyOrdered

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace Prod

@[to_additive]
instance instMul [Mul M] [Mul N] : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_mul [Mul M] [Mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_mul [Mul M] [Mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 :=
  rfl

@[to_additive (attr := simp)]
theorem mk_mul_mk [Mul M] [Mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
    (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) :=
  rfl

@[to_additive (attr := simp)]
theorem swap_mul [Mul M] [Mul N] (p q : M × N) : (p * q).swap = p.swap * q.swap :=
  rfl

@[to_additive]
theorem mul_def [Mul M] [Mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) :=
  rfl

@[to_additive]
theorem one_mk_mul_one_mk [Monoid M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) := by
  rw [mk_mul_mk, mul_one]

@[to_additive]
theorem mk_one_mul_mk_one [Mul M] [Monoid N] (a₁ a₂ : M) :
    (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) := by
  rw [mk_mul_mk, mul_one]

@[to_additive]
instance instOne [One M] [One N] : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := simp)]
theorem fst_one [One M] [One N] : (1 : M × N).1 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_one [One M] [One N] : (1 : M × N).2 = 1 :=
  rfl

@[to_additive]
theorem one_eq_mk [One M] [One N] : (1 : M × N) = (1, 1) :=
  rfl

@[to_additive (attr := simp)]
theorem mk_one_one [One M] [One N] : ((1 : M), (1 : N)) = 1 := rfl

@[to_additive (attr := simp)]
theorem mk_eq_one [One M] [One N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
  mk.inj_iff

@[to_additive (attr := simp)]
theorem swap_one [One M] [One N] : (1 : M × N).swap = 1 :=
  rfl

@[to_additive]
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  Prod.ext (mul_one p.1) (one_mul p.2)

@[to_additive]
instance instInv [Inv M] [Inv N] : Inv (M × N) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
theorem fst_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem snd_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_mk [Inv G] [Inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl

@[to_additive (attr := simp)]
theorem swap_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.swap = p.swap⁻¹ :=
  rfl

@[to_additive]
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { inv_inv := fun _ => Prod.ext (inv_inv _) (inv_inv _) }

@[to_additive]
instance instDiv [Div M] [Div N] : Div (M × N) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_div [Div G] [Div H] (a b : G × H) : (a / b).1 = a.1 / b.1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_div [Div G] [Div H] (a b : G × H) : (a / b).2 = a.2 / b.2 :=
  rfl

@[to_additive (attr := simp)]
theorem mk_div_mk [Div G] [Div H] (x₁ x₂ : G) (y₁ y₂ : H) :
    (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) :=
  rfl

@[to_additive (attr := simp)]
theorem swap_div [Div G] [Div H] (a b : G × H) : (a / b).swap = a.swap / b.swap :=
  rfl

@[to_additive]
instance instSemigroup [Semigroup M] [Semigroup N] : Semigroup (M × N) :=
  { mul_assoc := fun _ _ _ => mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩ }

@[to_additive]
instance instCommSemigroup [CommSemigroup G] [CommSemigroup H] : CommSemigroup (G × H) :=
  { mul_comm := fun _ _ => mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩ }

@[to_additive]
instance instMulOneClass [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) :=
  { one_mul := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
    mul_one := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩ }

@[to_additive]
instance instMonoid [Monoid M] [Monoid N] : Monoid (M × N) :=
  { npow := fun z a => ⟨Monoid.npow z a.1, Monoid.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    mul_assoc := mul_assoc }

@[to_additive Prod.subNegMonoid]
instance [DivInvMonoid G] [DivInvMonoid H] : DivInvMonoid (G × H) :=
  { div_eq_mul_inv := fun _ _ => mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩,
    zpow := fun z a => ⟨DivInvMonoid.zpow z a.1, DivInvMonoid.zpow z a.2⟩,
    zpow_zero' := fun _ => Prod.ext (DivInvMonoid.zpow_zero' _) (DivInvMonoid.zpow_zero' _),
    zpow_succ' := fun _ _ => Prod.ext (DivInvMonoid.zpow_succ' _ _) (DivInvMonoid.zpow_succ' _ _),
    zpow_neg' := fun _ _ => Prod.ext (DivInvMonoid.zpow_neg' _ _) (DivInvMonoid.zpow_neg' _ _) }

@[to_additive]
instance [DivisionMonoid G] [DivisionMonoid H] : DivisionMonoid (G × H) :=
  { mul_inv_rev := fun a b => Prod.ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun a b h =>
      Prod.ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }

@[to_additive SubtractionCommMonoid]
instance [DivisionCommMonoid G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H) :=
  { mul_comm := fun ⟨g₁ , h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }

@[to_additive]
instance instGroup [Group G] [Group H] : Group (G × H) :=
  { inv_mul_cancel := fun _ => mk.inj_iff.mpr ⟨inv_mul_cancel _, inv_mul_cancel _⟩ }

@[to_additive]
instance [Mul G] [Mul H] [IsLeftCancelMul G] [IsLeftCancelMul H] : IsLeftCancelMul (G × H) where
  mul_left_cancel _ _ _ h :=
      Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
instance [Mul G] [Mul H] [IsRightCancelMul G] [IsRightCancelMul H] : IsRightCancelMul (G × H) where
  mul_right_cancel _ _ _ h :=
      Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
instance [Mul G] [Mul H] [IsCancelMul G] [IsCancelMul H] : IsCancelMul (G × H) where

@[to_additive]
instance [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
instance [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
instance [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { mul_one := by simp,
    one_mul := by simp
    mul_left_cancel := by simp }

@[to_additive]
instance [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { mul_one := by simp,
    one_mul := by simp
    mul_right_cancel := by simp }

@[to_additive]
instance [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { mul_right_cancel := by simp only [mul_left_inj, imp_self, forall_const] }

@[to_additive]
instance instCommMonoid [CommMonoid M] [CommMonoid N] : CommMonoid (M × N) :=
  { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }

@[to_additive]
instance [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { mul_left_cancel := by simp }

@[to_additive]
instance instCommGroup [CommGroup G] [CommGroup H] : CommGroup (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }

end Prod

section
variable [Mul M] [Mul N]

@[to_additive AddSemiconjBy.prod]
theorem SemiconjBy.prod {x y z : M × N}
    (hm : SemiconjBy x.1 y.1 z.1) (hn : SemiconjBy x.2 y.2 z.2) : SemiconjBy x y z :=
  Prod.ext hm hn

@[to_additive]
theorem Prod.semiconjBy_iff {x y z : M × N} :
    SemiconjBy x y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2 := Prod.ext_iff

@[to_additive AddCommute.prod]
theorem Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2) : Commute x y :=
  .prod hm hn

@[to_additive]
theorem Prod.commute_iff {x y : M × N} :
    Commute x y ↔ Commute x.1 y.1 ∧ Commute x.2 y.2 := semiconjBy_iff

end

namespace MulHom

section Prod

variable (M N) [Mul M] [Mul N] [Mul P]

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `M`. -/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `A`"]
def fst : M × N →ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `B`"]
def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩

variable {M N}

@[to_additive (attr := simp)]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

/-- Combine two `MonoidHom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      "Combine two `AddMonoidHom`s `f : AddHom M N`, `g : AddHom M P` into
      `f.prod g : AddHom M (N × P)` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →ₙ* N) (g : M →ₙ* P) :
    M →ₙ* N × P where
  toFun := Pi.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
theorem prod_unique (f : M →ₙ* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap "`Prod.map` as an `AddMonoidHom`"]
def prodMap : M × N →ₙ* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
theorem prod_comp_prodMap (f : P →ₙ* M) (g : P →ₙ* N) (f' : M →ₙ* M') (g' : N →ₙ* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

/-- Coproduct of two `MulHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative codomain; for the general case, see `MulHom.noncommCoprod`) -/
@[to_additive
    "Coproduct of two `AddHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative codomain; for the general case, see `AddHom.noncommCoprod`)"]
def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive]
theorem comp_coprod {Q : Type*} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp

end Coprod

end MulHom

namespace MonoidHom

variable (M N) [MulOneClass M] [MulOneClass N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `A`"]
def fst : M × N →* M :=
  { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `B`"]
def snd : M × N →* N :=
  { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `A` to `A × B`."]
def inl : M →* M × N :=
  { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `B` to `A × B`."]
def inr : N →* M × N :=
  { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }

variable {M N}

@[to_additive (attr := simp)]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

@[to_additive (attr := simp)]
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl

@[to_additive (attr := simp)]
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl

@[to_additive (attr := simp)]
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl

@[to_additive (attr := simp)]
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl

@[to_additive]
theorem commute_inl_inr (m : M) (n : N) : Commute (inl M N m) (inr M N n) :=
  Commute.prod (.one_right m) (.one_left n)

section Prod

variable [MulOneClass P]

/-- Combine two `MonoidHom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      "Combine two `AddMonoidHom`s `f : M →+ N`, `g : M →+ P` into
      `f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →* N) (g : M →* P) :
    M →* N × P where
  toFun := Pi.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.prod g) = Pi.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M →* M') (g : N →* N')

/-- `prod.map` as a `MonoidHom`. -/
@[to_additive prodMap "`prod.map` as an `AddMonoidHom`."]
def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
theorem prod_comp_prodMap (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [CommMonoid P] (f : M →* P) (g : N →* P)

/-- Coproduct of two `MonoidHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative case; for the general case, see `MonoidHom.noncommCoprod`.)-/
@[to_additive
    "Coproduct of two `AddMonoidHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative case; for the general case, see `AddHom.noncommCoprod`.)"]
def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive (attr := simp)]
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]
theorem coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)

@[to_additive]
theorem comp_coprod {Q : Type*} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp

end Coprod

end MonoidHom

namespace MulEquiv

section

variable [MulOneClass M] [MulOneClass N]

/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[to_additive prodComm
      "The equivalence between `M × N` and `N × M` given by swapping the
      components is additive."]
def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodComm]
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl

@[to_additive (attr := simp) coe_prodComm_symm]
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl

variable {M' N' : Type*} [MulOneClass M'] [MulOneClass N']

section

variable (M N M' N')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[to_additive (attr := simps apply) prodProdProdComm
    "Four-way commutativity of `Prod`.\nThe name matches `mul_mul_mul_comm`"]
def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }

@[to_additive (attr := simp) prodProdProdComm_toEquiv]
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm M N M' N' : _ ≃ _) = Equiv.prodProdProdComm M N M' N' :=
  rfl

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N' :=
  rfl

end

/-- Product of multiplicative isomorphisms; the maps come from `Equiv.prodCongr`. -/
@[to_additive prodCongr "Product of additive isomorphisms; the maps come from `Equiv.prodCongr`."]
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (map_mul f _ _) (map_mul g _ _) }

/-- Multiplying by the trivial monoid doesn't change the structure. -/
@[to_additive uniqueProd "Multiplying by the trivial monoid doesn't change the structure."]
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }

/-- Multiplying by the trivial monoid doesn't change the structure. -/
@[to_additive prodUnique "Multiplying by the trivial monoid doesn't change the structure."]
def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }

end

section

variable [Monoid M] [Monoid N]

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[to_additive prodAddUnits
      "The additive monoid equivalence between additive units of a product
      of two additive monoids, and the product of the additive units of each additive monoid."]
def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ where
  toFun := (Units.map (MonoidHom.fst M N)).prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right_inv := fun ⟨u₁, u₂⟩ => by
    simp only [Units.map, MonoidHom.coe_fst, Units.inv_eq_val_inv,
      MonoidHom.coe_snd, MonoidHom.prod_apply, Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  map_mul' := MonoidHom.map_mul _

end

end MulEquiv

namespace Units

open MulOpposite

/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive (attr := simps)
      "Canonical homomorphism of additive monoids from `AddUnits α` into `α × αᵃᵒᵖ`.
      Used mainly to define the natural topology of `AddUnits α`."]
def embedProduct (α : Type*) [Monoid α] : αˣ →* α × αᵐᵒᵖ where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, eq_self_iff_true, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]

@[to_additive]
theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedProduct α) :=
  fun _ _ h => Units.ext <| (congr_arg Prod.fst h : _)

end Units

/-! ### Multiplication and division as homomorphisms -/


section BundledMulDiv

variable {α : Type*}

/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive (attr := simps) "Addition as an additive homomorphism."]
def mulMulHom [CommSemigroup α] :
    α × α →ₙ* α where
  toFun a := a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _

/-- Multiplication as a monoid homomorphism. -/
@[to_additive (attr := simps) "Addition as an additive monoid homomorphism."]
def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }

/-- Division as a monoid homomorphism. -/
@[to_additive (attr := simps) "Subtraction as an additive monoid homomorphism."]
def divMonoidHom [DivisionCommMonoid α] : α × α →* α where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _

end BundledMulDiv
