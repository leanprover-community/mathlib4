

import Mathlib.Tactic.Spread
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Group.WithOne.Defs

universe u v w

variable {α : Type u}

def WithZero (α) :=
  Option α

namespace WithZero

instance zero : Zero (WithZero α) :=
  ⟨none⟩

instance nontrivial [Nonempty α] : Nontrivial (WithZero α) :=
  Option.nontrivial

@[coe]
def coe : α → WithZero α :=
  Option.some

instance coeTC : CoeTC α (WithZero α) :=
  ⟨coe⟩

@[simp, norm_cast]
theorem coe_inj {a b : α} : (a : WithZero α) = b ↔ a = b :=
  Option.some_inj

end WithZero

end Mathlib.Algebra.Group.WithOne.Defs

variable {α β γ : Type _}

section Mathlib.Data.Option.NAry

def Option.map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=
  a.bind fun a => b.map <| f a

end Mathlib.Data.Option.NAry

section Mathlib.Algebra.GroupWithZero.WithZero

namespace WithZero

section One
variable [One α]

instance one : One (WithZero α) where
  __ := ‹One α›

@[simp, norm_cast] lemma coe_one : ((1 : α) : WithZero α) = 1 := rfl

end One

section Mul
variable [Mul α]

instance mulZeroClass : MulZeroClass (WithZero α) where
  mul := Option.map₂ (· * ·)
  zero_mul := sorry
  mul_zero := sorry

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithZero α) = a * b := rfl

end Mul

instance semigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
  __ := mulZeroClass
  mul_assoc _ _ _ := sorry

section MulOneClass
variable [MulOneClass α]

instance mulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where
  __ := mulZeroClass
  one_mul := sorry
  mul_one := sorry

end MulOneClass

section Pow
variable [One α] [Pow α ℕ]

instance pow : Pow (WithZero α) ℕ where
  pow x n := match x, n with
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)

end Pow

instance monoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where
  __ := mulZeroOneClass
  __ := semigroupWithZero
  npow n a := a ^ n
  npow_zero a := sorry
  npow_succ n a := sorry

section Inv
variable [Inv α]

instance inv : Inv (WithZero α) where inv a := Option.map (·⁻¹) a

@[simp, norm_cast] lemma coe_inv (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ := rfl

end Inv

section Div
variable [Div α]

instance div : Div (WithZero α) where div := Option.map₂ (· / ·)

end Div

section ZPow
variable [One α] [Pow α ℤ]

instance : Pow (WithZero α) ℤ where
  pow a n := match a, n with
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)

end ZPow

instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) where
  __ := monoidWithZero
  div_eq_mul_inv a b := sorry
  zpow n a := a ^ n
  zpow_zero' a := sorry
  zpow_succ' n a := sorry
  zpow_neg' _ a := sorry

section Group
variable [Group α]

/-- If `α` is a group then `WithZero α` is a group with zero. -/
instance groupWithZero : GroupWithZero (WithZero α) where
  __ := monoidWithZero
  __ := divInvMonoid
  __ := nontrivial
  inv_zero := sorry
  mul_inv_cancel a ha := by
    let x : ∃ a' : α, a' = a := sorry
    obtain ⟨a, rfl⟩ := x
    norm_cast
    apply mul_inv_cancel

end Group

end WithZero

end Mathlib.Algebra.GroupWithZero.WithZero
