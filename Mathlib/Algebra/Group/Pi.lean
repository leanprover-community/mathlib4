/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.group.pi
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Pairwise
import Mathbin.Algebra.Hom.GroupInstances
import Mathbin.Data.Pi.Algebra
import Mathbin.Data.Set.Function
import Mathbin.Tactic.PiInstances

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/


universe u v w

variable {ι α : Type _}

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

@[to_additive]
theorem Set.preimage_one {α β : Type _} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s
#align set.preimage_one Set.preimage_one

namespace Pi

@[to_additive]
instance semigroup [∀ i, Semigroup <| f i] : Semigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;> pi_instance_derive_field
#align pi.semigroup Pi.semigroup

instance semigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.semigroup_with_zero Pi.semigroupWithZero

@[to_additive]
instance commSemigroup [∀ i, CommSemigroup <| f i] : CommSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;> pi_instance_derive_field
#align pi.comm_semigroup Pi.commSemigroup

@[to_additive]
instance mulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_one_class Pi.mulOneClass

@[to_additive]
instance monoid [∀ i, Monoid <| f i] : Monoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := fun n x i => x i ^ n } <;>
    pi_instance_derive_field
#align pi.monoid Pi.monoid

@[to_additive]
instance commMonoid [∀ i, CommMonoid <| f i] : CommMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_monoid Pi.commMonoid

@[to_additive Pi.subNegMonoid]
instance [∀ i, DivInvMonoid <| f i] : DivInvMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive]
instance [∀ i, InvolutiveInv <| f i] : InvolutiveInv (∀ i, f i) := by
  refine_struct { inv := Inv.inv } <;> pi_instance_derive_field

@[to_additive Pi.subtractionMonoid]
instance [∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive Pi.subtractionCommMonoid]
instance [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i) :=
  { Pi.divisionMonoid, Pi.commSemigroup with }

@[to_additive]
instance group [∀ i, Group <| f i] : Group (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field
#align pi.group Pi.group

@[to_additive]
instance commGroup [∀ i, CommGroup <| f i] : CommGroup (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field
#align pi.comm_group Pi.commGroup

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] :
    LeftCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;> pi_instance_derive_field
#align pi.left_cancel_semigroup Pi.leftCancelSemigroup

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] :
    RightCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;> pi_instance_derive_field
#align pi.right_cancel_semigroup Pi.rightCancelSemigroup

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.left_cancel_monoid Pi.leftCancelMonoid

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow.. } <;>
    pi_instance_derive_field
#align pi.right_cancel_monoid Pi.rightCancelMonoid

@[to_additive AddCancelMonoid]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.cancel_monoid Pi.cancelMonoid

@[to_additive AddCancelCommMonoid]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.cancel_comm_monoid Pi.cancelCommMonoid

instance mulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_zero_class Pi.mulZeroClass

instance mulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_zero_one_class Pi.mulZeroOneClass

instance monoidWithZero [∀ i, MonoidWithZero <| f i] : MonoidWithZero (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.monoid_with_zero Pi.monoidWithZero

instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i : I, f i) :=
  by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_monoid_with_zero Pi.commMonoidWithZero

end Pi

namespace MulHom

@[to_additive]
theorem coe_mul {M N} {mM : Mul M} {mN : CommSemigroup N} (f g : M →ₙ* N) :
    (f * g : M → N) = fun x => f x * g x :=
  rfl
#align mul_hom.coe_mul MulHom.coe_mul

end MulHom

section MulHom

/-- A family of mul_hom `f a : γ →ₙ* β a` defines a mul_hom `pi.mul_hom f : γ →ₙ* Π a, β a`
given by `pi.mul_hom f x b = f b x`. -/
@[to_additive
      "A family of add_hom `f a : γ → β a` defines a add_hom `pi.add_hom\nf : γ → Π a, β a` given by `pi.add_hom f x b = f b x`.",
  simps]
def Pi.mulHom {γ : Type w} [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i) :
    γ →ₙ* ∀ i, f i where 
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y
#align pi.mul_hom Pi.mulHom

@[to_additive]
theorem Pi.mul_hom_injective {γ : Type w} [Nonempty I] [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.mulHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iff.mp h : _) i)
#align pi.mul_hom_injective Pi.mul_hom_injective

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`pi.monoid_mul_hom f : γ →* Π a, β a` given by `pi.monoid_mul_hom f x b = f b x`. -/
@[to_additive
      "A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid\nhomomorphism `pi.add_monoid_hom f : γ →+ Π a, β a` given by `pi.add_monoid_hom f x b\n= f b x`.",
  simps]
def Pi.monoidHom {γ : Type w} [∀ i, MulOneClass (f i)] [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }
#align pi.monoid_hom Pi.monoidHom

@[to_additive]
theorem Pi.monoid_hom_injective {γ : Type w} [Nonempty I] [∀ i, MulOneClass (f i)] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.monoidHom g) :=
  Pi.mul_hom_injective (fun i => (g i).toMulHom) hg
#align pi.monoid_hom_injective Pi.monoid_hom_injective

variable (f) [∀ i, Mul (f i)]

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `function.eval i` as a `mul_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive semigroups at a\npoint is an additive semigroup homomorphism.\nThis is `function.eval i` as an `add_hom`.",
  simps]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ*
      f i where 
  toFun g := g i
  map_mul' x y := Pi.mul_apply _ _ i
#align pi.eval_mul_hom Pi.evalMulHom

/-- `function.const` as a `mul_hom`. -/
@[to_additive "`function.const` as an `add_hom`.", simps]
def Pi.constMulHom (α β : Type _) [Mul β] :
    β →ₙ* α → β where 
  toFun := Function.const α
  map_mul' _ _ := rfl
#align pi.const_mul_hom Pi.constMulHom

/-- Coercion of a `mul_hom` into a function is itself a `mul_hom`.
See also `mul_hom.eval`. -/
@[to_additive
      "Coercion of an `add_hom` into a function is itself a `add_hom`.\nSee also `add_hom.eval`. ",
  simps]
def MulHom.coeFn (α β : Type _) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where 
  toFun g := g
  map_mul' x y := rfl
#align mul_hom.coe_fn MulHom.coeFn

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive semigroup homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive semigroup homomorphism `f` between `α` and `β`",
  simps]
protected def MulHom.compLeft {α β : Type _} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type _) :
    (I → α) →ₙ* I → β where 
  toFun h := f ∘ h
  map_mul' _ _ := by ext <;> simp
#align mul_hom.comp_left MulHom.compLeft

end MulHom

section MonoidHom

variable (f) [∀ i, MulOneClass (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `function.eval i` as a `monoid_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive monoids at a\npoint is an additive monoid homomorphism.\nThis is `function.eval i` as an `add_monoid_hom`.",
  simps]
def Pi.evalMonoidHom (i : I) :
    (∀ i, f i) →* f i where 
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' x y := Pi.mul_apply _ _ i
#align pi.eval_monoid_hom Pi.evalMonoidHom

/-- `function.const` as a `monoid_hom`. -/
@[to_additive "`function.const` as an `add_monoid_hom`.", simps]
def Pi.constMonoidHom (α β : Type _) [MulOneClass β] :
    β →* α → β where 
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl
#align pi.const_monoid_hom Pi.constMonoidHom

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[to_additive
      "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.\n\nSee also `add_monoid_hom.eval`. ",
  simps]
def MonoidHom.coeFn (α β : Type _) [MulOneClass α] [CommMonoid β] :
    (α →* β) →* α → β where 
  toFun g := g
  map_one' := rfl
  map_mul' x y := rfl
#align monoid_hom.coe_fn MonoidHom.coeFn

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive monoid homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive monoid homomorphism `f` between `α` and `β`",
  simps]
protected def MonoidHom.compLeft {α β : Type _} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type _) : (I → α) →* I → β where 
  toFun h := f ∘ h
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
#align monoid_hom.comp_left MonoidHom.compLeft

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `one_hom` version of `pi.mul_single`. -/
@[to_additive ZeroHom.single
      "The zero-preserving homomorphism including a single value\ninto a dependent family of values, as functions supported at a point.\n\nThis is the `zero_hom` version of `pi.single`."]
def OneHom.single [∀ i, One <| f i] (i : I) :
    OneHom (f i) (∀ i, f i) where 
  toFun := mulSingle i
  map_one' := mulSingle_one i
#align one_hom.single OneHom.single

@[simp, to_additive]
theorem OneHom.single_apply [∀ i, One <| f i] (i : I) (x : f i) :
    OneHom.single f i x = mulSingle i x :=
  rfl
#align one_hom.single_apply OneHom.single_apply

/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `monoid_hom` version of `pi.mul_single`. -/
@[to_additive
      "The additive monoid homomorphism including a single additive\nmonoid into a dependent family of additive monoids, as functions supported at a point.\n\nThis is the `add_monoid_hom` version of `pi.single`."]
def MonoidHom.single [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.single f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }
#align monoid_hom.single MonoidHom.single

@[simp, to_additive]
theorem MonoidHom.single_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    MonoidHom.single f i x = mulSingle i x :=
  rfl
#align monoid_hom.single_apply MonoidHom.single_apply

/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps]
def MulHom.single [∀ i, MulZeroClass <| f i] (i : I) :
    f i →ₙ* ∀ i, f i where 
  toFun := single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _
#align mul_hom.single MulHom.single

variable {f}

@[to_additive]
theorem Pi.mul_single_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.single f i).map_mul x y
#align pi.mul_single_mul Pi.mul_single_mul

@[to_additive]
theorem Pi.mul_single_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.single f i).map_inv x
#align pi.mul_single_inv Pi.mul_single_inv

@[to_additive]
theorem Pi.single_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.single f i).map_div x y
#align pi.single_div Pi.single_div

theorem Pi.single_mul [∀ i, MulZeroClass <| f i] (i : I) (x y : f i) :
    single i (x * y) = single i x * single i y :=
  (MulHom.single f i).map_mul x y
#align pi.single_mul Pi.single_mul

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `commute.map` -/
@[to_additive
      "The injection into an additive pi group at different indices commutes.\n\nFor injections of commuting elements at the same index, see `add_commute.map`"]
theorem Pi.mul_single_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  by_cases h1 : i = k;
  · subst h1
    simp [hij]
  by_cases h2 : j = k;
  · subst h2
    simp [hij]
  simp [h1, h2]
#align pi.mul_single_commute Pi.mul_single_commute

/-- The injection into a pi group with the same values commutes. -/
@[to_additive "The injection into an additive pi group with the same values commutes."]
theorem Pi.mul_single_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mul_single_commute hij _ _
#align pi.mul_single_apply_commute Pi.mul_single_apply_commute

@[to_additive update_eq_sub_add_single]
theorem Pi.update_eq_div_mul_single [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h]
#align pi.update_eq_div_mul_single Pi.update_eq_div_mul_single

@[to_additive Pi.single_add_single_eq_single_add_single]
theorem Pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single {M : Type _} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    mulSingle k u * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n :=
  by 
  refine' ⟨fun h => _, _⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := (congr_fun h m).symm
    have hn := (congr_fun h n).symm
    simp only [mul_apply, mul_single_apply, if_pos rfl] at hk hl hm hn
    rcases eq_or_ne k m with (rfl | hkm)
    · refine' Or.inl ⟨rfl, not_ne_iff.mp fun hln => (hv _).elim⟩
      rcases eq_or_ne k l with (rfl | hkl)
      · rwa [if_neg hln.symm, if_neg hln.symm, one_mul, one_mul] at hn
      · rwa [if_neg hkl.symm, if_neg hln, one_mul, one_mul] at hl
    · rcases eq_or_ne m n with (rfl | hmn)
      · rcases eq_or_ne k l with (rfl | hkl)
        · rw [if_neg hkm.symm, if_neg hkm.symm, one_mul, if_pos rfl] at hm
          exact Or.inr (Or.inr ⟨hm, rfl, rfl⟩)
        · simpa only [if_neg hkm, if_neg hkl, mul_one] using hk
      · rw [if_neg hkm.symm, if_neg hmn, one_mul, mul_one] at hm
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1
        rw [if_neg hkm, if_neg hkm, one_mul, mul_one] at hk
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1
        exact Or.inr (Or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · rfl
    · apply mul_comm
    · simp_rw [← Pi.mul_single_mul, h, mul_single_one]
#align
  pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single Pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single

end Single

namespace Function

@[simp, to_additive]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i 1
#align function.update_one Function.update_one

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· * ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_mul Function.update_mul

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun i => Inv.inv) f₁ i x₁ j).symm
#align function.update_inv Function.update_inv

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· / ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_div Function.update_div

variable [One α] [Nonempty ι] {a : α}

@[simp, to_additive]
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1
#align function.const_eq_one Function.const_eq_one

@[to_additive]
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  const_eq_one.Not
#align function.const_ne_one Function.const_ne_one

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· * ·)
#align set.piecewise_mul Set.piecewise_mul

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹
#align set.piecewise_inv Set.piecewise_inv

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· / ·)
#align set.piecewise_div Set.piecewise_div

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive Function.ExtendByZero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where 
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1
#align function.extend_by_one.hom Function.ExtendByOne.hom

end Extend

