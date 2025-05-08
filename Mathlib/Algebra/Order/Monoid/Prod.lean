/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Prod.RevLex

/-! # Products of ordered monoids -/

assert_not_exists MonoidWithZero

namespace Prod

variable {α β : Type*}

@[to_additive]
instance [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β] : IsOrderedMonoid (α × β) where
  mul_le_mul_left _ _ h _ := ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩

@[to_additive]
instance instIsOrderedCancelMonoid
    [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α × β) :=
  { le_of_mul_le_mul_left :=
      fun _ _ _ h ↦ ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
instance [LE α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
    ExistsMulOfLE (α × β) :=
  ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), Prod.ext hc hd⟩⟩

@[to_additive]
instance [Mul α] [LE α] [CanonicallyOrderedMul α]
    [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (α × β) :=
  { (inferInstance : ExistsMulOfLE _) with
      le_self_mul := fun _ _ ↦ le_def.mpr ⟨le_self_mul, le_self_mul⟩ }

namespace Lex

@[to_additive]
instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [MulLeftStrictMono α]
    [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ hxy z := (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left' hxy _)
    (fun hxy => le_iff.2 <|
      Or.inr ⟨by simp only [ofLex_mul, fst_mul, hxy.1], mul_le_mul_left' hxy.2 _⟩)

@[to_additive]
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ := mul_le_mul_left'
  le_of_mul_le_mul_left _ _ _ hxyz := (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

end Lex

namespace RevLex

@[to_additive]
instance [One α] : One (RevLex α) where
  one := toRevLex 1

@[to_additive (attr := simp)]
theorem toRevLex_one [One α] : toRevLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofRevLex_one [One α] : (ofRevLex 1 : α) = 1 := rfl

@[to_additive]
instance [h : Mul α] : Mul (RevLex α) where
  mul a b := toRevLex (ofRevLex a * ofRevLex b)

@[to_additive (attr := simp)]
theorem toRevLex_mul [Mul α] (a b : α) : toRevLex (a * b) = toRevLex a * toRevLex b := rfl

@[to_additive (attr := simp)]
theorem ofRevLex_mul [Mul α] (a b : RevLex α) : ofRevLex (a * b) = ofRevLex a * ofRevLex b := rfl

@[to_additive]
instance [Monoid α] [Monoid β] : Monoid (α ×ᵣ β) where
  mul_assoc a b c := by
    simp_rw [HMul.hMul, Mul.mul, ofRevLex_toRevLex, mul_assoc]
  one_mul a := by
    simp_rw [HMul.hMul, Mul.mul]
    simp
  mul_one a := by
    simp_rw [HMul.hMul, Mul.mul]
    simp

@[to_additive]
instance [CommMonoid α] [CommMonoid β] : CommMonoid (α ×ᵣ β) where
  mul_comm a b := by
    simp_rw [HMul.hMul, Mul.mul, mul_comm]

@[to_additive]
instance [CommGroup α] [CommGroup β] : CommGroup (α ×ᵣ β) where
  inv a := toRevLex ((ofRevLex a)⁻¹)
  inv_mul_cancel a := ofRevLex_inj.mp (by simp)

@[to_additive]
instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CommMonoid β] [PartialOrder β] [MulLeftStrictMono β] :
    IsOrderedMonoid (α ×ᵣ β) where
  mul_le_mul_left _ _ hxy z := (le_iff.1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left' hxy _)
    (fun hxy => le_iff.2 <| Or.inr
      ⟨by simp only [ofRevLex_mul, snd_mul, hxy.1],  mul_le_mul_left' hxy.2 _⟩)

@[to_additive]
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α ×ᵣ β) where
  mul_le_mul_left _ _ := mul_le_mul_left'
  le_of_mul_le_mul_left _ _ _ hxyz := (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

@[to_additive]
theorem LexEquiv_mul [PartialOrder α] [Monoid α] [PartialOrder β] [Monoid β] (x y : α ×ₗ β) :
    LexEquiv α β (x * y) = LexEquiv α β x * LexEquiv α β y := by
  simp [LexEquiv, ← toRevLex_mul]

end RevLex

end Prod
