/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Hom.Units

#align_import algebra.group.prod from "leanprover-community/mathlib"@"cd391184c85986113f8c00844cfe6dda1d34be3d"

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`Monoid`, `Group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `MonoidHom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `Prod.fst` and `Prod.snd`
  as `MonoidHom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g` : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prodMap g : M × N → M' × N'`: `prod.map f g` as a `MonoidHom`,
  sends `(x, y)` to `(f x, g y)`.

## Main declarations

* `mulMulHom`/`mulMonoidHom`/`mulMonoidWithZeroHom`: Multiplication bundled as a
  multiplicative/monoid/monoid with zero homomorphism.
* `divMonoidHom`/`divMonoidWithZeroHom`: Division bundled as a monoid/monoid with zero
  homomorphism.
-/


variable {A : Type*} {B : Type*} {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace Prod

@[to_additive]
instance instMul [Mul M] [Mul N] : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_mul [Mul M] [Mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 :=
  rfl
#align prod.fst_mul Prod.fst_mul
#align prod.fst_add Prod.fst_add

@[to_additive (attr := simp)]
theorem snd_mul [Mul M] [Mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 :=
  rfl
#align prod.snd_mul Prod.snd_mul
#align prod.snd_add Prod.snd_add

@[to_additive (attr := simp)]
theorem mk_mul_mk [Mul M] [Mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
    (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) :=
  rfl
#align prod.mk_mul_mk Prod.mk_mul_mk
#align prod.mk_add_mk Prod.mk_add_mk

@[to_additive (attr := simp)]
theorem swap_mul [Mul M] [Mul N] (p q : M × N) : (p * q).swap = p.swap * q.swap :=
  rfl
#align prod.swap_mul Prod.swap_mul
#align prod.swap_add Prod.swap_add

@[to_additive]
theorem mul_def [Mul M] [Mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) :=
  rfl
#align prod.mul_def Prod.mul_def
#align prod.add_def Prod.add_def

@[to_additive]
theorem one_mk_mul_one_mk [Monoid M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) :=
  by rw [mk_mul_mk, mul_one]
     -- 🎉 no goals
#align prod.one_mk_mul_one_mk Prod.one_mk_mul_one_mk
#align prod.zero_mk_add_zero_mk Prod.zero_mk_add_zero_mk

@[to_additive]
theorem mk_one_mul_mk_one [Mul M] [Monoid N] (a₁ a₂ : M) :
    (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) :=
  by rw [mk_mul_mk, mul_one]
     -- 🎉 no goals
#align prod.mk_one_mul_mk_one Prod.mk_one_mul_mk_one
#align prod.mk_zero_add_mk_zero Prod.mk_zero_add_mk_zero

@[to_additive]
instance instOne [One M] [One N] : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := simp)]
theorem fst_one [One M] [One N] : (1 : M × N).1 = 1 :=
  rfl
#align prod.fst_one Prod.fst_one
#align prod.fst_zero Prod.fst_zero

@[to_additive (attr := simp)]
theorem snd_one [One M] [One N] : (1 : M × N).2 = 1 :=
  rfl
#align prod.snd_one Prod.snd_one
#align prod.snd_zero Prod.snd_zero

@[to_additive]
theorem one_eq_mk [One M] [One N] : (1 : M × N) = (1, 1) :=
  rfl
#align prod.one_eq_mk Prod.one_eq_mk
#align prod.zero_eq_mk Prod.zero_eq_mk

@[to_additive (attr := simp)]
theorem mk_eq_one [One M] [One N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
  mk.inj_iff
#align prod.mk_eq_one Prod.mk_eq_one
#align prod.mk_eq_zero Prod.mk_eq_zero

@[to_additive (attr := simp)]
theorem swap_one [One M] [One N] : (1 : M × N).swap = 1 :=
  rfl
#align prod.swap_one Prod.swap_one
#align prod.swap_zero Prod.swap_zero

@[to_additive]
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  ext (mul_one p.1) (one_mul p.2)
#align prod.fst_mul_snd Prod.fst_mul_snd
#align prod.fst_add_snd Prod.fst_add_snd

@[to_additive]
instance instInv [Inv M] [Inv N] : Inv (M × N) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
theorem fst_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.1 = p.1⁻¹ :=
  rfl
#align prod.fst_inv Prod.fst_inv
#align prod.fst_neg Prod.fst_neg

@[to_additive (attr := simp)]
theorem snd_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.2 = p.2⁻¹ :=
  rfl
#align prod.snd_inv Prod.snd_inv
#align prod.snd_neg Prod.snd_neg

@[to_additive (attr := simp)]
theorem inv_mk [Inv G] [Inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  rfl
#align prod.inv_mk Prod.inv_mk
#align prod.neg_mk Prod.neg_mk

@[to_additive (attr := simp)]
theorem swap_inv [Inv G] [Inv H] (p : G × H) : p⁻¹.swap = p.swap⁻¹ :=
  rfl
#align prod.swap_inv Prod.swap_inv
#align prod.swap_neg Prod.swap_neg

@[to_additive]
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { inv_inv := fun _ => ext (inv_inv _) (inv_inv _) }

@[to_additive]
instance instDiv [Div M] [Div N] : Div (M × N) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_div [Div G] [Div H] (a b : G × H) : (a / b).1 = a.1 / b.1 :=
  rfl
#align prod.fst_div Prod.fst_div
#align prod.fst_sub Prod.fst_sub

@[to_additive (attr := simp)]
theorem snd_div [Div G] [Div H] (a b : G × H) : (a / b).2 = a.2 / b.2 :=
  rfl
#align prod.snd_div Prod.snd_div
#align prod.snd_sub Prod.snd_sub

@[to_additive (attr := simp)]
theorem mk_div_mk [Div G] [Div H] (x₁ x₂ : G) (y₁ y₂ : H) :
    (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) :=
  rfl
#align prod.mk_div_mk Prod.mk_div_mk
#align prod.mk_sub_mk Prod.mk_sub_mk

@[to_additive (attr := simp)]
theorem swap_div [Div G] [Div H] (a b : G × H) : (a / b).swap = a.swap / b.swap :=
  rfl
#align prod.swap_div Prod.swap_div
#align prod.swap_sub Prod.swap_sub

instance [MulZeroClass M] [MulZeroClass N] : MulZeroClass (M × N) :=
  { zero_mul := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩,
    mul_zero := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩ }

@[to_additive]
instance instSemigroup [Semigroup M] [Semigroup N] : Semigroup (M × N) :=
  { mul_assoc := fun _ _ _ => mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩ }

@[to_additive]
instance instCommSemigroup [CommSemigroup G] [CommSemigroup H] : CommSemigroup (G × H) :=
  { mul_comm := fun _ _ => mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩ }

instance [SemigroupWithZero M] [SemigroupWithZero N] : SemigroupWithZero (M × N) :=
  { zero_mul := by simp,
                   -- 🎉 no goals
    mul_zero := by simp }
                   -- 🎉 no goals

@[to_additive]
instance instMulOneClass [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) :=
  { one_mul := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
    mul_one := fun a => Prod.recOn a fun _ _ => mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩ }

@[to_additive]
instance instMonoid [Monoid M] [Monoid N] : Monoid (M × N) :=
  { npow := fun z a => ⟨Monoid.npow z a.1, Monoid.npow z a.2⟩,
    npow_zero := fun z => ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun z a => ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
                  -- 🎉 no goals
    mul_one := by simp }
                  -- 🎉 no goals

@[to_additive Prod.subNegMonoid]
instance [DivInvMonoid G] [DivInvMonoid H] : DivInvMonoid (G × H) :=
  { div_eq_mul_inv := fun _ _ => mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩,
    zpow := fun z a => ⟨DivInvMonoid.zpow z a.1, DivInvMonoid.zpow z a.2⟩,
    zpow_zero' := fun _ => ext (DivInvMonoid.zpow_zero' _) (DivInvMonoid.zpow_zero' _),
    zpow_succ' := fun _ _ => ext (DivInvMonoid.zpow_succ' _ _) (DivInvMonoid.zpow_succ' _ _),
    zpow_neg' := fun _ _ => ext (DivInvMonoid.zpow_neg' _ _) (DivInvMonoid.zpow_neg' _ _) }

@[to_additive]
instance [DivisionMonoid G] [DivisionMonoid H] : DivisionMonoid (G × H) :=
  { mul_inv_rev := fun a b => ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun a b h =>
      ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }
                  -- 🎉 no goals

@[to_additive SubtractionCommMonoid]
instance [DivisionCommMonoid G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H) :=
  { mul_comm := fun ⟨g₁ , h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }
                                           -- ⊢ (fst✝ * g₁, snd✝ * h₁) = (fst✝, snd✝) * (g₁, h₁)
                                                                                     -- 🎉 no goals

@[to_additive]
instance instGroup [Group G] [Group H] : Group (G × H) :=
  { mul_left_inv := fun _ => mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩ }

@[to_additive]
instance [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { mul_left_cancel := fun _ _ _ h =>
      Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2) }

@[to_additive]
instance [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { mul_right_cancel := fun _ _ _ h =>
      Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2) }

@[to_additive]
instance [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { mul_one := by simp,
                  -- 🎉 no goals
                  -- 🎉 no goals
    one_mul := by simp }

@[to_additive]
instance [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { mul_one := by simp,
                  -- 🎉 no goals
                  -- 🎉 no goals
    one_mul := by simp }

@[to_additive]
instance [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { mul_right_cancel := by simp only [mul_left_inj, imp_self, forall_const] }
                           -- 🎉 no goals

@[to_additive]
instance instCommMonoid [CommMonoid M] [CommMonoid N] : CommMonoid (M × N) :=
  { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }
                                          -- 🎉 no goals

@[to_additive]
instance [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }
                                          -- 🎉 no goals

instance [MulZeroOneClass M] [MulZeroOneClass N] : MulZeroOneClass (M × N) :=
  { zero_mul := by simp,
                   -- 🎉 no goals
    mul_zero := by simp }
                   -- 🎉 no goals

instance [MonoidWithZero M] [MonoidWithZero N] : MonoidWithZero (M × N) :=
  { zero_mul := by simp,
                   -- 🎉 no goals
    mul_zero := by simp }
                   -- 🎉 no goals

instance [CommMonoidWithZero M] [CommMonoidWithZero N] : CommMonoidWithZero (M × N) :=
  { zero_mul := by simp,
                   -- 🎉 no goals
    mul_zero := by simp }
                   -- 🎉 no goals

@[to_additive]
instance instCommGroup [CommGroup G] [CommGroup H] : CommGroup (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }
                                          -- 🎉 no goals

end Prod

namespace MulHom

section Prod

variable (M N) [Mul M] [Mul N] [Mul P]

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `A`"]
def fst : M × N →ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩
#align mul_hom.fst MulHom.fst
#align add_hom.fst AddHom.fst

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `B`"]
def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩
#align mul_hom.snd MulHom.snd
#align add_hom.snd AddHom.snd

variable {M N}

@[to_additive (attr := simp)]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align mul_hom.coe_fst MulHom.coe_fst
#align add_hom.coe_fst AddHom.coe_fst

@[to_additive (attr := simp)]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align mul_hom.coe_snd MulHom.coe_snd
#align add_hom.coe_snd AddHom.coe_snd

/-- Combine two `MonoidHom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      "Combine two `AddMonoidHom`s `f : AddHom M N`, `g : AddHom M P` into
      `f.prod g : AddHom M (N × P)` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →ₙ* N) (g : M →ₙ* P) :
    M →ₙ* N × P where
  toFun := Pi.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)
#align mul_hom.prod MulHom.prod
#align add_hom.prod AddHom.prod

@[to_additive coe_prod]
theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align mul_hom.coe_prod MulHom.coe_prod
#align add_hom.coe_prod AddHom.coe_prod

@[to_additive (attr := simp) prod_apply]
theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.prod g x = (f x, g x) :=
  rfl
#align mul_hom.prod_apply MulHom.prod_apply
#align add_hom.prod_apply AddHom.prod_apply

@[to_additive (attr := simp) fst_comp_prod]
theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl
#align mul_hom.fst_comp_prod MulHom.fst_comp_prod
#align add_hom.fst_comp_prod AddHom.fst_comp_prod

@[to_additive (attr := simp) snd_comp_prod]
theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl
#align mul_hom.snd_comp_prod MulHom.snd_comp_prod
#align add_hom.snd_comp_prod AddHom.snd_comp_prod

@[to_additive (attr := simp) prod_unique]
theorem prod_unique (f : M →ₙ* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
                  -- 🎉 no goals
#align mul_hom.prod_unique MulHom.prod_unique
#align add_hom.prod_unique AddHom.prod_unique

end Prod

section Prod_map

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap "`prod.map` as an `AddMonoidHom`"]
def prodMap : M × N →ₙ* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))
#align mul_hom.prod_map MulHom.prodMap
#align add_hom.prod_map AddHom.prodMap

@[to_additive prodMap_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl
#align mul_hom.prod_map_def MulHom.prodMap_def
#align add_hom.prod_map_def AddHom.prodMap_def

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align mul_hom.coe_prod_map MulHom.coe_prodMap
#align add_hom.coe_prod_map AddHom.coe_prodMap

@[to_additive prod_comp_prodMap]
theorem prod_comp_prodMap (f : P →ₙ* M) (g : P →ₙ* N) (f' : M →ₙ* M') (g' : N →ₙ* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
#align mul_hom.prod_comp_prod_map MulHom.prod_comp_prodMap
#align add_hom.prod_comp_prod_map AddHom.prod_comp_prodMap

end Prod_map

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

/-- Coproduct of two `MulHom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `AddHom`s with the same codomain:
      `f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align mul_hom.coprod MulHom.coprod
#align add_hom.coprod AddHom.coprod

@[to_additive (attr := simp)]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align mul_hom.coprod_apply MulHom.coprod_apply
#align add_hom.coprod_apply AddHom.coprod_apply

@[to_additive]
theorem comp_coprod {Q : Type*} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
                  -- 🎉 no goals
#align mul_hom.comp_coprod MulHom.comp_coprod
#align add_hom.comp_coprod AddHom.comp_coprod

end Coprod

end MulHom

namespace MonoidHom

variable (M N) [MulOneClass M] [MulOneClass N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `A`"]
def fst : M × N →* M :=
  { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }
#align monoid_hom.fst MonoidHom.fst
#align add_monoid_hom.fst AddMonoidHom.fst

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive
      "Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `B`"]
def snd : M × N →* N :=
  { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }
#align monoid_hom.snd MonoidHom.snd
#align add_monoid_hom.snd AddMonoidHom.snd

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `A` to `A × B`."]
def inl : M →* M × N :=
  { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }
#align monoid_hom.inl MonoidHom.inl
#align add_monoid_hom.inl AddMonoidHom.inl

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      "Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `B` to `A × B`."]
def inr : N →* M × N :=
  { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }
#align monoid_hom.inr MonoidHom.inr
#align add_monoid_hom.inr AddMonoidHom.inr

variable {M N}

@[to_additive (attr := simp)]
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl
#align monoid_hom.coe_fst MonoidHom.coe_fst
#align add_monoid_hom.coe_fst AddMonoidHom.coe_fst

@[to_additive (attr := simp)]
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl
#align monoid_hom.coe_snd MonoidHom.coe_snd
#align add_monoid_hom.coe_snd AddMonoidHom.coe_snd

@[to_additive (attr := simp)]
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl
#align monoid_hom.inl_apply MonoidHom.inl_apply
#align add_monoid_hom.inl_apply AddMonoidHom.inl_apply

@[to_additive (attr := simp)]
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl
#align monoid_hom.inr_apply MonoidHom.inr_apply
#align add_monoid_hom.inr_apply AddMonoidHom.inr_apply

@[to_additive (attr := simp)]
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl
#align monoid_hom.fst_comp_inl MonoidHom.fst_comp_inl
#align add_monoid_hom.fst_comp_inl AddMonoidHom.fst_comp_inl

@[to_additive (attr := simp)]
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl
#align monoid_hom.snd_comp_inl MonoidHom.snd_comp_inl
#align add_monoid_hom.snd_comp_inl AddMonoidHom.snd_comp_inl

@[to_additive (attr := simp)]
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl
#align monoid_hom.fst_comp_inr MonoidHom.fst_comp_inr
#align add_monoid_hom.fst_comp_inr AddMonoidHom.fst_comp_inr

@[to_additive (attr := simp)]
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl
#align monoid_hom.snd_comp_inr MonoidHom.snd_comp_inr
#align add_monoid_hom.snd_comp_inr AddMonoidHom.snd_comp_inr

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
#align monoid_hom.prod MonoidHom.prod
#align add_monoid_hom.prod AddMonoidHom.prod

@[to_additive coe_prod]
theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.prod g) = Pi.prod f g :=
  rfl
#align monoid_hom.coe_prod MonoidHom.coe_prod
#align add_monoid_hom.coe_prod AddMonoidHom.coe_prod

@[to_additive (attr := simp) prod_apply]
theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) :=
  rfl
#align monoid_hom.prod_apply MonoidHom.prod_apply
#align add_monoid_hom.prod_apply AddMonoidHom.prod_apply

@[to_additive (attr := simp) fst_comp_prod]
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl
#align monoid_hom.fst_comp_prod MonoidHom.fst_comp_prod
#align add_monoid_hom.fst_comp_prod AddMonoidHom.fst_comp_prod

@[to_additive (attr := simp) snd_comp_prod]
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl
#align monoid_hom.snd_comp_prod MonoidHom.snd_comp_prod
#align add_monoid_hom.snd_comp_prod AddMonoidHom.snd_comp_prod

@[to_additive (attr := simp) prod_unique]
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
                  -- 🎉 no goals
#align monoid_hom.prod_unique MonoidHom.prod_unique
#align add_monoid_hom.prod_unique AddMonoidHom.prod_unique

end Prod

section Prod_map

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M →* M') (g : N →* N')

/-- `prod.map` as a `MonoidHom`. -/
@[to_additive prodMap "`prod.map` as an `AddMonoidHom`."]
def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))
#align monoid_hom.prod_map MonoidHom.prodMap
#align add_monoid_hom.prod_map AddMonoidHom.prodMap

@[to_additive prodMap_def]
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl
#align monoid_hom.prod_map_def MonoidHom.prodMap_def
#align add_monoid_hom.prod_map_def AddMonoidHom.prodMap_def

@[to_additive (attr := simp) coe_prodMap]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align monoid_hom.coe_prod_map MonoidHom.coe_prodMap
#align add_monoid_hom.coe_prod_map AddMonoidHom.coe_prodMap

@[to_additive prod_comp_prodMap]
theorem prod_comp_prodMap (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
#align monoid_hom.prod_comp_prod_map MonoidHom.prod_comp_prodMap
#align add_monoid_hom.prod_comp_prod_map AddMonoidHom.prod_comp_prodMap

end Prod_map

section Coprod

variable [CommMonoid P] (f : M →* P) (g : N →* P)

/-- Coproduct of two `MonoidHom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive
      "Coproduct of two `AddMonoidHom`s with the same codomain:
      `f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)
#align monoid_hom.coprod MonoidHom.coprod
#align add_monoid_hom.coprod AddMonoidHom.coprod

@[to_additive (attr := simp)]
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl
#align monoid_hom.coprod_apply MonoidHom.coprod_apply
#align add_monoid_hom.coprod_apply AddMonoidHom.coprod_apply

@[to_additive (attr := simp)]
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]
                  -- 🎉 no goals
#align monoid_hom.coprod_comp_inl MonoidHom.coprod_comp_inl
#align add_monoid_hom.coprod_comp_inl AddMonoidHom.coprod_comp_inl

@[to_additive (attr := simp)]
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]
                  -- 🎉 no goals
#align monoid_hom.coprod_comp_inr MonoidHom.coprod_comp_inr
#align add_monoid_hom.coprod_comp_inr AddMonoidHom.coprod_comp_inr

@[to_additive (attr := simp)]
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]
                  -- 🎉 no goals
#align monoid_hom.coprod_unique MonoidHom.coprod_unique
#align add_monoid_hom.coprod_unique AddMonoidHom.coprod_unique

@[to_additive (attr := simp)]
theorem coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)
#align monoid_hom.coprod_inl_inr MonoidHom.coprod_inl_inr
#align add_monoid_hom.coprod_inl_inr AddMonoidHom.coprod_inl_inr

@[to_additive]
theorem comp_coprod {Q : Type*} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp
                  -- 🎉 no goals
#align monoid_hom.comp_coprod MonoidHom.comp_coprod
#align add_monoid_hom.comp_coprod AddMonoidHom.comp_coprod

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
#align mul_equiv.prod_comm MulEquiv.prodComm
#align add_equiv.prod_comm AddEquiv.prodComm

@[to_additive (attr := simp) coe_prodComm]
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm MulEquiv.coe_prodComm
#align add_equiv.coe_prod_comm AddEquiv.coe_prodComm

@[to_additive (attr := simp) coe_prodComm_symm]
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl
#align mul_equiv.coe_prod_comm_symm MulEquiv.coe_prodComm_symm
#align add_equiv.coe_prod_comm_symm AddEquiv.coe_prodComm_symm

variable {M' N' : Type*} [MulOneClass M'] [MulOneClass N']

section

variable (M N M' N')

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[to_additive (attr := simps apply) prodProdProdComm
    "Four-way commutativity of `prod`.\nThe name matches `mul_mul_mul_comm`"]
def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }
#align mul_equiv.prod_prod_prod_comm MulEquiv.prodProdProdComm
#align add_equiv.prod_prod_prod_comm AddEquiv.prodProdProdComm

@[to_additive (attr := simp) prodProdProdComm_toEquiv]
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm M N M' N' : _ ≃ _) = Equiv.prodProdProdComm M N M' N' :=
  rfl
#align mul_equiv.prod_prod_prod_comm_to_equiv MulEquiv.prodProdProdComm_toEquiv
#align add_equiv.sum_sum_sum_comm_to_equiv AddEquiv.prodProdProdComm_toEquiv

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N' :=
  rfl
#align mul_equiv.prod_prod_prod_comm_symm MulEquiv.prodProdProdComm_symm

end

/-- Product of multiplicative isomorphisms; the maps come from `Equiv.prodCongr`.-/
@[to_additive prodCongr "Product of additive isomorphisms; the maps come from `Equiv.prodCongr`."]
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (f.map_mul _ _) (g.map_mul _ _) }
#align mul_equiv.prod_congr MulEquiv.prodCongr
#align add_equiv.prod_congr AddEquiv.prodCongr

/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive uniqueProd "Multiplying by the trivial monoid doesn't change the structure."]
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }
#align mul_equiv.unique_prod MulEquiv.uniqueProd
#align add_equiv.unique_prod AddEquiv.uniqueProd

/-- Multiplying by the trivial monoid doesn't change the structure.-/
@[to_additive prodUnique "Multiplying by the trivial monoid doesn't change the structure."]
def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }
#align mul_equiv.prod_unique MulEquiv.prodUnique
#align add_equiv.prod_unique AddEquiv.prodUnique

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
                                                -- 🎉 no goals
                                                         -- 🎉 no goals
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right_inv := fun ⟨u₁, u₂⟩ => by
    simp only [Units.map, MonoidHom.coe_fst, Units.inv_eq_val_inv,
      MonoidHom.coe_snd, MonoidHom.prod_apply, Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
    -- 🎉 no goals
  map_mul' := MonoidHom.map_mul _
#align mul_equiv.prod_units MulEquiv.prodUnits
#align add_equiv.prod_add_units AddEquiv.prodAddUnits

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
    -- 🎉 no goals
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]
                     -- 🎉 no goals
#align units.embed_product Units.embedProduct
#align add_units.embed_product AddUnits.embedProduct
#align units.embed_product_apply Units.embedProduct_apply
#align add_units.embed_product_apply AddUnits.embedProduct_apply

@[to_additive]
theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedProduct α) :=
  fun _ _ h => Units.ext <| (congr_arg Prod.fst h : _)
#align units.embed_product_injective Units.embedProduct_injective
#align add_units.embed_product_injective AddUnits.embedProduct_injective

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
#align mul_mul_hom mulMulHom
#align add_add_hom addAddHom
#align mul_mul_hom_apply mulMulHom_apply
#align add_add_hom_apply addAddHom_apply

/-- Multiplication as a monoid homomorphism. -/
@[to_additive (attr := simps) "Addition as an additive monoid homomorphism."]
def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }
#align mul_monoid_hom mulMonoidHom
#align add_add_monoid_hom addAddMonoidHom
#align mul_monoid_hom_apply mulMonoidHom_apply
#align add_add_monoid_hom_apply addAddMonoidHom_apply

/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
def mulMonoidWithZeroHom [CommMonoidWithZero α] : α × α →*₀ α :=
  { mulMonoidHom with map_zero' := mul_zero _ }
#align mul_monoid_with_zero_hom mulMonoidWithZeroHom
#align mul_monoid_with_zero_hom_apply mulMonoidWithZeroHom_apply

/-- Division as a monoid homomorphism. -/
@[to_additive (attr := simps) "Subtraction as an additive monoid homomorphism."]
def divMonoidHom [DivisionCommMonoid α] : α × α →* α where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _
#align div_monoid_hom divMonoidHom
#align sub_add_monoid_hom subAddMonoidHom
#align div_monoid_hom_apply divMonoidHom_apply
#align sub_add_monoid_hom_apply subAddMonoidHom_apply

/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
def divMonoidWithZeroHom [CommGroupWithZero α] : α × α →*₀ α where
  toFun a := a.1 / a.2
  map_zero' := zero_div _
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _
#align div_monoid_with_zero_hom divMonoidWithZeroHom
#align div_monoid_with_zero_hom_apply divMonoidWithZeroHom_apply

end BundledMulDiv
