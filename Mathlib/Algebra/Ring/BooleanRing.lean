/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `BooleanRing`: a typeclass for rings where multiplication is idempotent.
* `BooleanRing.toBooleanAlgebra`: Turn a Boolean ring into a Boolean algebra.
* `BooleanAlgebra.toBooleanRing`: Turn a Boolean algebra into a Boolean ring.
* `AsBoolAlg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `AsBoolRing`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `BooleanAlgebraOfBooleanRing` and
  `BooleanRingOfBooleanAlgebra`.
* Type-synonyms `AsBoolAlg` and `AsBoolRing`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`ofBoolAlg`/`toBoolAlg`/`ofBoolRing`/`toBoolRing` explicitly.

## Tags

boolean ring, boolean algebra
-/

open scoped symmDiff

variable {α β γ : Type*}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ring α where
  /-- Multiplication in a Boolean ring is idempotent. -/
  isIdempotentElem (a : α) : IsIdempotentElem a

namespace BooleanRing

variable [BooleanRing α] (a b : α)

@[scoped simp]
lemma mul_self : a * a = a := IsIdempotentElem.eq (isIdempotentElem a)

instance : Std.IdempotentOp (α := α) (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[scoped simp]
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

@[scoped simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]

theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

@[simp]
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [left_eq_add] at this

@[scoped simp]
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]

-- Note [lower instance priority]
instance (priority := 100) toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }

end BooleanRing

instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolAlg (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolAlg α` and `α`. -/
def toBoolAlg : α ≃ AsBoolAlg α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolAlg α`. -/
def ofBoolAlg : AsBoolAlg α ≃ α :=
  Equiv.refl _

@[simp]
theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg :=
  rfl

@[simp]
theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg :=
  rfl

@[simp]
theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a :=
  rfl

@[simp]
theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a :=
  rfl

theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b :=
  Iff.rfl

theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolAlg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
def sup : Max α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
def inf : Min α :=
  ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf
open BooleanAlgebraOfBooleanRing

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  dsimp only [(· ⊔ ·)]
  ring

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  ring

theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  dsimp only [(· ⊔ ·)]
  ring

theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  dsimp only [(· ⊓ ·)]
  ring

theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc, mul_self, add_assoc, add_self, add_zero]

theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add, mul_add, mul_self, ← mul_assoc, mul_self, add_assoc, add_self, add_zero]

theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]

theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_add]

/-- The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
def toBooleanAlgebra : BooleanAlgebra α :=
  { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, add_comm a 1,
                                                     add_assoc, add_self, add_zero]
    bot := 0
    bot_le := fun a => show 0 + a + 0 * a = a by rw [zero_mul, zero_add, add_zero]
    compl := fun a => 1 + a
    inf_compl_le_bot := fun a =>
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by simp [mul_add, mul_self, add_self]
    top_le_sup_compl := fun a => by
      change
        1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) =
          a + (1 + a) + a * (1 + a)
      norm_num [mul_add, mul_self, add_self]
      rw [← add_assoc, add_self] }

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.toBooleanAlgebra

end BooleanRing

open BooleanRing

instance : BooleanAlgebra (AsBoolAlg α) :=
  @BooleanRing.toBooleanAlgebra α _

@[simp]
theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 :=
  rfl

@[simp]
theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 :=
  rfl

@[simp]
theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
theorem ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a :=
  rfl

@[simp]
theorem ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b) :=
  rfl

private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

@[simp]
theorem ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

@[simp]
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} :
    ofBoolAlg a * ofBoolAlg b = ofBoolAlg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolAlg α) _ _ _

@[simp]
theorem toBoolAlg_zero : toBoolAlg (0 : α) = ⊥ :=
  rfl

@[simp]
theorem toBoolAlg_one : toBoolAlg (1 : α) = ⊤ :=
  rfl

@[simp]
theorem toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b :=
  rfl

@[simp]
theorem toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b :=
  rfl

@[simp]
theorem toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b :=
  (ofBoolAlg_symmDiff a b).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
protected def RingHom.asBoolAlg (f : α →+* β) : BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β) where
  toFun := toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]
theorem RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _ :=
  rfl

@[simp]
theorem RingHom.asBoolAlg_comp (g : β →+* γ) (f : α →+* β) :
    (g.comp f).asBoolAlg = g.asBoolAlg.comp f.asBoolAlg :=
  rfl

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolRing (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolRing α` and `α`. -/
def toBoolRing : α ≃ AsBoolRing α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolRing α`. -/
def ofBoolRing : AsBoolRing α ≃ α :=
  Equiv.refl _

@[simp]
theorem toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing :=
  rfl

@[simp]
theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing :=
  rfl

@[simp]
theorem toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a :=
  rfl

@[simp]
theorem ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a :=
  rfl

theorem toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b :=
  Iff.rfl

theorem ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolRing α) :=
  ‹Inhabited α›

-- See note [reducible non-instances]
/-- Every generalized Boolean algebra has the structure of a nonunital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
abbrev GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α] :
    NonUnitalCommRing α where
  add := (· ∆ ·)
  add_assoc := symmDiff_assoc
  zero := ⊥
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq
  neg := id
  neg_add_cancel := symmDiff_self
  add_comm := symmDiff_comm
  mul := (· ⊓ ·)
  mul_assoc := inf_assoc
  mul_comm := inf_comm
  left_distrib := inf_symmDiff_distrib_left
  right_distrib := inf_symmDiff_distrib_right
  nsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; nsmulRec
  zsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; letI : Neg α := ⟨id⟩; zsmulRec

instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolRing α) :=
  @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

-- See note [reducible non-instances]
/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
abbrev BooleanAlgebra.toBooleanRing : BooleanRing α where
  __ := GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

instance : BooleanRing (AsBoolRing α) :=
  @BooleanAlgebra.toBooleanRing α _

@[simp]
theorem ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥ :=
  rfl

@[simp]
theorem ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤ :=
  rfl

@[simp]
theorem ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a :=
  rfl

@[simp]
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
theorem ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b :=
  rfl

@[simp]
theorem ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} :
    ofBoolRing a ≤ ofBoolRing b ↔ a * b = a :=
  inf_eq_left.symm

@[simp]
theorem toBoolRing_bot : toBoolRing (⊥ : α) = 0 :=
  rfl

@[simp]
theorem toBoolRing_top : toBoolRing (⊤ : α) = 1 :=
  rfl

@[simp]
theorem toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b :=
  rfl

@[simp]
theorem toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b :=
  rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
protected def BoundedLatticeHom.asBoolRing (f : BoundedLatticeHom α β) :
    AsBoolRing α →+* AsBoolRing β where
  toFun := toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

@[simp]
theorem BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = RingHom.id _ :=
  rfl

@[simp]
theorem BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing :=
  rfl

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps!]
def OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (AsBoolRing α) ≃o α :=
  ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps!]
def RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (AsBoolAlg α) ≃+* α :=
  { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

open Bool

instance : Zero Bool where zero := false

instance : One Bool where one := true

instance : Add Bool where add := xor

instance : Neg Bool where neg := id

instance : Sub Bool where sub := xor

instance : Mul Bool where mul := and

instance : BooleanRing Bool where
  add_assoc := xor_assoc
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg_add_cancel := Bool.xor_self
  add_comm := xor_comm
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  isIdempotentElem := Bool.and_self
  zero_mul _ := rfl
  mul_zero a := by cases a <;> rfl
  nsmul := nsmulRec
  zsmul := zsmulRec
