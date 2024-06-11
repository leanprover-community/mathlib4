/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Data.Int.Cast.Prod
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Order.Group.Prod
import Mathlib.Algebra.Order.Ring.Defs

#align_import algebra.ring.prod from "leanprover-community/mathlib"@"cd391184c85986113f8c00844cfe6dda1d34be3d"

/-!
# Semiring, ring etc structures on `R × S`

In this file we define two-binop (`Semiring`, `Ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `RingHom`s and similarly for
`NonUnitalRingHom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `Prod.fst` and `Prod.snd`
  as `RingHom`s;
* `f.prod g : R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : R × S → R' × S'`: `Prod.map f g` as a `RingHom`,
  sends `(x, y)` to `(f x, g y)`.
-/


variable {α β R R' S S' T T' : Type*}

namespace Prod

/-- Product of two distributive types is distributive. -/
instance instDistrib [Distrib R] [Distrib S] : Distrib (R × S) :=
  { left_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩
    right_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩ }

/-- Product of two `NonUnitalNonAssocSemiring`s is a `NonUnitalNonAssocSemiring`. -/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { inferInstanceAs (AddCommMonoid (R × S)),
    inferInstanceAs (Distrib (R × S)),
    inferInstanceAs (MulZeroClass (R × S)) with }

/-- Product of two `NonUnitalSemiring`s is a `NonUnitalSemiring`. -/
instance instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] :
    NonUnitalSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (SemigroupWithZero (R × S)) with }

/-- Product of two `NonAssocSemiring`s is a `NonAssocSemiring`. -/
instance instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] :
    NonAssocSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (MulZeroOneClass (R × S)),
    inferInstanceAs (AddMonoidWithOne (R × S)) with }

/-- Product of two semirings is a semiring. -/
instance instSemiring [Semiring R] [Semiring S] : Semiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (MonoidWithZero (R × S)) with }

/-- Product of two `NonUnitalCommSemiring`s is a `NonUnitalCommSemiring`. -/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] :
    NonUnitalCommSemiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }

/-- Product of two commutative semirings is a commutative semiring. -/
instance instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { inferInstanceAs (Semiring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] :
    NonUnitalNonAssocRing (R × S) :=
  { inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (NonUnitalNonAssocSemiring (R × S)) with }

instance instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonUnitalSemiring (R × S)) with }

instance instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }

/-- Product of two rings is a ring. -/
instance instRing [Ring R] [Ring S] : Ring (R × S) :=
  { inferInstanceAs (Semiring (R × S)),
    inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }

/-- Product of two `NonUnitalCommRing`s is a `NonUnitalCommRing`. -/
instance instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] :
    NonUnitalCommRing (R × S) :=
  { inferInstanceAs (NonUnitalRing (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }

/-- Product of two commutative rings is a commutative ring. -/
instance instCommRing [CommRing R] [CommRing S] : CommRing (R × S) :=
  { inferInstanceAs (Ring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align non_unital_ring_hom.fst NonUnitalRingHom.fst

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
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
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl
#align non_unital_ring_hom.prod_apply NonUnitalRingHom.prod_apply

@[simp]
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl
#align non_unital_ring_hom.fst_comp_prod NonUnitalRingHom.fst_comp_prod

@[simp]
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
#align non_unital_ring_hom.snd_comp_prod NonUnitalRingHom.snd_comp_prod

theorem prod_unique (f : R →ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]
#align non_unital_ring_hom.prod_unique NonUnitalRingHom.prod_unique

end Prod

section prodMap

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]
variable (f : R →ₙ+* R') (g : S →ₙ+* S')

/-- `Prod.map` as a `NonUnitalRingHom`. -/
def prodMap : R × S →ₙ+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
#align non_unital_ring_hom.prod_map NonUnitalRingHom.prodMap

theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
#align non_unital_ring_hom.prod_map_def NonUnitalRingHom.prodMap_def

@[simp]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align non_unital_ring_hom.coe_prod_map NonUnitalRingHom.coe_prodMap

theorem prod_comp_prodMap (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
#align non_unital_ring_hom.prod_comp_prod_map NonUnitalRingHom.prod_comp_prodMap

end prodMap

end NonUnitalRingHom

namespace RingHom

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`. -/
def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
#align ring_hom.fst RingHom.fst

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`. -/
def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
#align ring_hom.snd RingHom.snd

instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (fst R S) := ⟨(⟨⟨·, 0⟩, rfl⟩)⟩
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (snd R S) := ⟨(⟨⟨0, ·⟩, rfl⟩)⟩

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
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl
#align ring_hom.prod_apply RingHom.prod_apply

@[simp]
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl
#align ring_hom.fst_comp_prod RingHom.fst_comp_prod

@[simp]
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
#align ring_hom.snd_comp_prod RingHom.snd_comp_prod

theorem prod_unique (f : R →+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]
#align ring_hom.prod_unique RingHom.prod_unique

end Prod

section prodMap

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]
variable (f : R →+* R') (g : S →+* S')

/-- `Prod.map` as a `RingHom`. -/
def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
#align ring_hom.prod_map RingHom.prodMap

theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
#align ring_hom.prod_map_def RingHom.prodMap_def

@[simp]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
#align ring_hom.coe_prod_map RingHom.coe_prodMap

theorem prod_comp_prodMap (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
#align ring_hom.prod_comp_prod_map RingHom.prod_comp_prodMap

end prodMap

end RingHom

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']

/-- Swapping components as an equivalence of (semi)rings. -/
def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }
#align ring_equiv.prod_comm RingEquiv.prodComm

@[simp]
theorem coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap :=
  rfl
#align ring_equiv.coe_prod_comm RingEquiv.coe_prodComm

@[simp]
theorem coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap :=
  rfl
#align ring_equiv.coe_prod_comm_symm RingEquiv.coe_prodComm_symm

@[simp]
theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S :=
  RingHom.ext fun _ => rfl
#align ring_equiv.fst_comp_coe_prod_comm RingEquiv.fst_comp_coe_prodComm

@[simp]
theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S :=
  RingHom.ext fun _ => rfl
#align ring_equiv.snd_comp_coe_prod_comm RingEquiv.snd_comp_coe_prodComm

section

variable (R R' S S')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' :=
  { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }
#align ring_equiv.prod_prod_prod_comm RingEquiv.prodProdProdComm

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S' :=
  rfl
#align ring_equiv.prod_prod_prod_comm_symm RingEquiv.prodProdProdComm_symm

@[simp]
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' :=
  rfl
#align ring_equiv.prod_prod_prod_comm_to_add_equiv RingEquiv.prodProdProdComm_toAddEquiv

@[simp]
theorem prodProdProdComm_toMulEquiv :
    (prodProdProdComm R R' S S' : _ ≃* _) = MulEquiv.prodProdProdComm R R' S S' :=
  rfl
#align ring_equiv.prod_prod_prod_comm_to_mul_equiv RingEquiv.prodProdProdComm_toMulEquiv

@[simp]
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' :=
  rfl
#align ring_equiv.prod_prod_prod_comm_to_equiv RingEquiv.prodProdProdComm_toEquiv

end

variable (R S) [Subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps]
def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
#align ring_equiv.prod_zero_ring RingEquiv.prodZeroRing
#align ring_equiv.prod_zero_ring_symm_apply RingEquiv.prodZeroRing_symm_apply
#align ring_equiv.prod_zero_ring_apply RingEquiv.prodZeroRing_apply

/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps]
def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  left_inv x := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
#align ring_equiv.zero_ring_prod RingEquiv.zeroRingProd
#align ring_equiv.zero_ring_prod_symm_apply RingEquiv.zeroRingProd_symm_apply
#align ring_equiv.zero_ring_prod_apply RingEquiv.zeroRingProd_apply

end RingEquiv

/-- The product of two nontrivial rings is not a domain -/
theorem false_of_nontrivial_of_product_domain (R S : Type*) [Ring R] [Ring S] [IsDomain (R × S)]
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
  { inferInstanceAs (Semiring (α × β)), inferInstanceAs (OrderedAddCommMonoid (α × β)) with
    zero_le_one := ⟨zero_le_one, zero_le_one⟩
    mul_le_mul_of_nonneg_left := fun _ _ _ hab hc =>
      ⟨mul_le_mul_of_nonneg_left hab.1 hc.1, mul_le_mul_of_nonneg_left hab.2 hc.2⟩
    mul_le_mul_of_nonneg_right := fun _ _ _ hab hc =>
      ⟨mul_le_mul_of_nonneg_right hab.1 hc.1, mul_le_mul_of_nonneg_right hab.2 hc.2⟩ }

instance [OrderedCommSemiring α] [OrderedCommSemiring β] : OrderedCommSemiring (α × β) :=
  { inferInstanceAs (OrderedSemiring (α × β)), inferInstanceAs (CommSemiring (α × β)) with }

-- Porting note: compile fails with `inferInstanceAs (OrderedSemiring (α × β))`
instance [OrderedRing α] [OrderedRing β] : OrderedRing (α × β) :=
  { inferInstanceAs (Ring (α × β)), inferInstanceAs (OrderedAddCommGroup (α × β)) with
    zero_le_one := ⟨zero_le_one, zero_le_one⟩
    mul_nonneg := fun _ _ ha hb => ⟨mul_nonneg ha.1 hb.1, mul_nonneg ha.2 hb.2⟩ }

instance [OrderedCommRing α] [OrderedCommRing β] : OrderedCommRing (α × β) :=
  { inferInstanceAs (OrderedRing (α × β)), inferInstanceAs (CommRing (α × β)) with }
