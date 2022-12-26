/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.ring.prod
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Prod
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Order.Monoid.Prod

/-!
# Semiring, ring etc structures on `R × S`

In this file we define two-binop (`semiring`, `ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `ring_hom`s and similarly for
`non_unital_ring_hom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `prod.fst` and `prod.snd`
  as `ring_hom`s;
* `f.prod g : `R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : `R × S → R' × S'`: `prod.map f g` as a `ring_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/


variable {α β R R' S S' T T' : Type _}

namespace Prod

/-- Product of two distributive types is distributive. -/
instance [Distrib R] [Distrib S] : Distrib (R × S) :=
  { Prod.hasAdd, Prod.hasMul with
    left_distrib := fun a b c => mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩
    right_distrib := fun a b c => mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩ }

/-- Product of two `non_unital_non_assoc_semiring`s is a `non_unital_non_assoc_semiring`. -/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { Prod.addCommMonoid, Prod.mulZeroClass, Prod.distrib with }

/-- Product of two `non_unital_semiring`s is a `non_unital_semiring`. -/
instance [NonUnitalSemiring R] [NonUnitalSemiring S] : NonUnitalSemiring (R × S) :=
  { Prod.nonUnitalNonAssocSemiring, Prod.semigroup with }

/-- Product of two `non_assoc_semiring`s is a `non_assoc_semiring`. -/
instance [NonAssocSemiring R] [NonAssocSemiring S] : NonAssocSemiring (R × S) :=
  { Prod.nonUnitalNonAssocSemiring, Prod.mulOneClass, Prod.addMonoidWithOne with }

/-- Product of two semirings is a semiring. -/
instance [Semiring R] [Semiring S] : Semiring (R × S) :=
  { Prod.addCommMonoid, Prod.monoidWithZero, Prod.distrib, Prod.addMonoidWithOne with }

/-- Product of two `non_unital_comm_semiring`s is a `non_unital_comm_semiring`. -/
instance [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] : NonUnitalCommSemiring (R × S) :=
  { Prod.nonUnitalSemiring, Prod.commSemigroup with }

/-- Product of two commutative semirings is a commutative semiring. -/
instance [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { Prod.semiring, Prod.commMonoid with }

instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] : NonUnitalNonAssocRing (R × S) :=
  { Prod.addCommGroup, Prod.nonUnitalNonAssocSemiring with }

instance [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { Prod.addCommGroup, Prod.nonUnitalSemiring with }

instance [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { Prod.addCommGroup, Prod.nonAssocSemiring, Prod.addGroupWithOne with }

/-- Product of two rings is a ring. -/
instance [Ring R] [Ring S] : Ring (R × S) :=
  { Prod.addCommGroup, Prod.addGroupWithOne, Prod.semiring with }

/-- Product of two `non_unital_comm_ring`s is a `non_unital_comm_ring`. -/
instance [NonUnitalCommRing R] [NonUnitalCommRing S] : NonUnitalCommRing (R × S) :=
  { Prod.nonUnitalRing, Prod.commSemigroup with }

/-- Product of two commutative rings is a commutative ring. -/
instance [CommRing R] [CommRing S] : CommRing (R × S) :=
  { Prod.ring, Prod.commMonoid with }

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align non_unital_ring_hom.fst NonUnitalRingHom.fst

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd : R × S →ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
#align non_unital_ring_hom.snd NonUnitalRingHom.snd

variable {R S}

@[simp]
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl
#align non_unital_ring_hom.coe_fst NonUnitalRingHom.coe_fst

@[simp]
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl
#align non_unital_ring_hom.coe_snd NonUnitalRingHom.coe_snd

section Prod

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

/-- Combine two non-unital ring homomorphisms `f : R →ₙ+* S`, `g : R →ₙ+* T` into
`f.prod g : R →ₙ+* S × T` given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
#align non_unital_ring_hom.prod NonUnitalRingHom.prod

@[simp]
theorem prod_apply (x) : f.Prod g x = (f x, g x) :=
  rfl
#align non_unital_ring_hom.prod_apply NonUnitalRingHom.prod_apply

@[simp]
theorem fst_comp_prod : (fst S T).comp (f.Prod g) = f :=
  ext fun x => rfl
#align non_unital_ring_hom.fst_comp_prod NonUnitalRingHom.fst_comp_prod

@[simp]
theorem snd_comp_prod : (snd S T).comp (f.Prod g) = g :=
  ext fun x => rfl
#align non_unital_ring_hom.snd_comp_prod NonUnitalRingHom.snd_comp_prod

theorem prod_unique (f : R →ₙ+* S × T) : ((fst S T).comp f).Prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align non_unital_ring_hom.prod_unique NonUnitalRingHom.prod_unique

end Prod

section Prod_map

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]

variable (f : R →ₙ+* R') (g : S →ₙ+* S')

/-- `prod.map` as a `non_unital_ring_hom`. -/
def prodMap : R × S →ₙ+* R' × S' :=
  (f.comp (fst R S)).Prod (g.comp (snd R S))
#align non_unital_ring_hom.prod_map NonUnitalRingHom.prodMap

theorem prod_map_def : prodMap f g = (f.comp (fst R S)).Prod (g.comp (snd R S)) :=
  rfl
#align non_unital_ring_hom.prod_map_def NonUnitalRingHom.prod_map_def

@[simp]
theorem coe_prod_map : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align non_unital_ring_hom.coe_prod_map NonUnitalRingHom.coe_prod_map

theorem prod_comp_prod_map (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align non_unital_ring_hom.prod_comp_prod_map NonUnitalRingHom.prod_comp_prod_map

end Prod_map

end NonUnitalRingHom

namespace RingHom

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align ring_hom.fst RingHom.fst

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
#align ring_hom.snd RingHom.snd

variable {R S}

@[simp]
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl
#align ring_hom.coe_fst RingHom.coe_fst

@[simp]
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl
#align ring_hom.coe_snd RingHom.coe_snd

section Prod

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  { MonoidHom.prod (f : R →* S) (g : R →* T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
#align ring_hom.prod RingHom.prod

@[simp]
theorem prod_apply (x) : f.Prod g x = (f x, g x) :=
  rfl
#align ring_hom.prod_apply RingHom.prod_apply

@[simp]
theorem fst_comp_prod : (fst S T).comp (f.Prod g) = f :=
  ext fun x => rfl
#align ring_hom.fst_comp_prod RingHom.fst_comp_prod

@[simp]
theorem snd_comp_prod : (snd S T).comp (f.Prod g) = g :=
  ext fun x => rfl
#align ring_hom.snd_comp_prod RingHom.snd_comp_prod

theorem prod_unique (f : R →+* S × T) : ((fst S T).comp f).Prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply, Prod.mk.eta]
#align ring_hom.prod_unique RingHom.prod_unique

end Prod

section Prod_map

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]

variable (f : R →+* R') (g : S →+* S')

/-- `prod.map` as a `ring_hom`. -/
def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).Prod (g.comp (snd R S))
#align ring_hom.prod_map RingHom.prodMap

theorem prod_map_def : prodMap f g = (f.comp (fst R S)).Prod (g.comp (snd R S)) :=
  rfl
#align ring_hom.prod_map_def RingHom.prod_map_def

@[simp]
theorem coe_prod_map : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align ring_hom.coe_prod_map RingHom.coe_prod_map

theorem prod_comp_prod_map (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prod_map g').comp (f.Prod g) = (f'.comp f).Prod (g'.comp g) :=
  rfl
#align ring_hom.prod_comp_prod_map RingHom.prod_comp_prod_map

end Prod_map

end RingHom

namespace RingEquiv

variable {R S} [NonAssocSemiring R] [NonAssocSemiring S]

/-- Swapping components as an equivalence of (semi)rings. -/
def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }
#align ring_equiv.prod_comm RingEquiv.prodComm

@[simp]
theorem coe_prod_comm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap :=
  rfl
#align ring_equiv.coe_prod_comm RingEquiv.coe_prod_comm

@[simp]
theorem coe_prod_comm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap :=
  rfl
#align ring_equiv.coe_prod_comm_symm RingEquiv.coe_prod_comm_symm

@[simp]
theorem fst_comp_coe_prod_comm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S :=
  RingHom.ext fun _ => rfl
#align ring_equiv.fst_comp_coe_prod_comm RingEquiv.fst_comp_coe_prod_comm

@[simp]
theorem snd_comp_coe_prod_comm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S :=
  RingHom.ext fun _ => rfl
#align ring_equiv.snd_comp_coe_prod_comm RingEquiv.snd_comp_coe_prod_comm

variable (R S) [Subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps]
def prodZeroRing : R ≃+* R × S where 
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x <;> simp
#align ring_equiv.prod_zero_ring RingEquiv.prodZeroRing

/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps]
def zeroRingProd : R ≃+* S × R where 
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x <;> simp
#align ring_equiv.zero_ring_prod RingEquiv.zeroRingProd

end RingEquiv

/-- The product of two nontrivial rings is not a domain -/
theorem false_of_nontrivial_of_product_domain (R S : Type _) [Ring R] [Ring S] [IsDomain (R × S)]
    [Nontrivial R] [Nontrivial S] : False := by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm
#align false_of_nontrivial_of_product_domain false_of_nontrivial_of_product_domain

/-! ### Order -/


instance [OrderedSemiring α] [OrderedSemiring β] : OrderedSemiring (α × β) :=
  { Prod.semiring, Prod.partialOrder _ _ with
    add_le_add_left := fun _ _ => add_le_add_left
    zero_le_one := ⟨zero_le_one, zero_le_one⟩
    mul_le_mul_of_nonneg_left := fun a b c hab hc =>
      ⟨mul_le_mul_of_nonneg_left hab.1 hc.1, mul_le_mul_of_nonneg_left hab.2 hc.2⟩
    mul_le_mul_of_nonneg_right := fun a b c hab hc =>
      ⟨mul_le_mul_of_nonneg_right hab.1 hc.1, mul_le_mul_of_nonneg_right hab.2 hc.2⟩ }

instance [OrderedCommSemiring α] [OrderedCommSemiring β] : OrderedCommSemiring (α × β) :=
  { Prod.commSemiring, Prod.orderedSemiring with }

instance [OrderedRing α] [OrderedRing β] : OrderedRing (α × β) :=
  { Prod.ring, Prod.orderedSemiring with
    mul_nonneg := fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_nonneg ha.2 hb.2⟩ }

instance [OrderedCommRing α] [OrderedCommRing β] : OrderedCommRing (α × β) :=
  { Prod.commRing, Prod.orderedRing with }

