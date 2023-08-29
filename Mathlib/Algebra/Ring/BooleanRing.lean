/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathlib.Algebra.PUnitInstances
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Order.Hom.Lattice

#align_import algebra.ring.boolean_ring from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

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


variable {α β γ : Type*}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ring α where
  /-- Multiplication in a boolean ring is idempotent. -/
  mul_self : ∀ a : α, a * a = a
#align boolean_ring BooleanRing

section BooleanRing

variable [BooleanRing α] (a b : α)

instance : IsIdempotent α (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[simp]
theorem mul_self : a * a = a :=
  BooleanRing.mul_self _
#align mul_self mul_self

@[simp]
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [self_eq_add_left] at this
  -- 🎉 no goals
#align add_self add_self

@[simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
                      -- 🎉 no goals
    _ = -a + -a + a := by rw [← neg_add_self, add_assoc]
                          -- 🎉 no goals
    _ = a := by rw [add_self, zero_add]
                -- 🎉 no goals
#align neg_eq neg_eq

theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]
                    -- 🎉 no goals
#align add_eq_zero' add_eq_zero'

@[simp]
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [self_eq_add_right] at this
  -- 🎉 no goals
#align mul_add_mul mul_add_mul

@[simp]
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]
                                         -- 🎉 no goals
#align sub_eq_add sub_eq_add

@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]
                                                 -- 🎉 no goals
#align mul_one_add_self mul_one_add_self

-- Note [lower instance priority]
instance (priority := 100) BooleanRing.toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }
                              -- 🎉 no goals
#align boolean_ring.to_comm_ring BooleanRing.toCommRing

end BooleanRing

instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolAlg (α : Type*) :=
  α
#align as_boolalg AsBoolAlg

/-- The "identity" equivalence between `AsBoolAlg α` and `α`. -/
def toBoolAlg : α ≃ AsBoolAlg α :=
  Equiv.refl _
#align to_boolalg toBoolAlg

/-- The "identity" equivalence between `α` and `AsBoolAlg α`. -/
def ofBoolAlg : AsBoolAlg α ≃ α :=
  Equiv.refl _
#align of_boolalg ofBoolAlg

@[simp]
theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg :=
  rfl
#align to_boolalg_symm_eq toBoolAlg_symm_eq

@[simp]
theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg :=
  rfl
#align of_boolalg_symm_eq ofBoolAlg_symm_eq

@[simp]
theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a :=
  rfl
#align to_boolalg_of_boolalg toBoolAlg_ofBoolAlg

@[simp]
theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a :=
  rfl
#align of_boolalg_to_boolalg ofBoolAlg_toBoolAlg

-- Porting note: simp can prove this -- @[simp]
theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b :=
  Iff.rfl
#align to_boolalg_inj toBoolAlg_inj

-- Porting note: simp can prove this -- @[simp]
theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b :=
  Iff.rfl
#align of_boolalg_inj ofBoolAlg_inj

instance [Inhabited α] : Inhabited (AsBoolAlg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
def sup : Sup α :=
  ⟨fun x y => x + y + x * y⟩
#align boolean_ring.has_sup BooleanRing.sup

/-- The meet operation in a Boolean ring is `x * y`. -/
def inf : Inf α :=
  ⟨(· * ·)⟩
#align boolean_ring.has_inf BooleanRing.inf

-- Porting note: TODO: add priority 100. lower instance priority
scoped [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.sup
scoped [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.inf
open BooleanAlgebraOfBooleanRing

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  dsimp only [(· ⊔ ·)]
  -- ⊢ a + b + a * b = b + a + b * a
  ring
  -- 🎉 no goals
#align boolean_ring.sup_comm BooleanRing.sup_comm

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  -- ⊢ a * b = b * a
  ring
  -- 🎉 no goals
#align boolean_ring.inf_comm BooleanRing.inf_comm

theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  dsimp only [(· ⊔ ·)]
  -- ⊢ a + b + a * b + c + (a + b + a * b) * c = a + (b + c + b * c) + a * (b + c + …
  ring
  -- 🎉 no goals
#align boolean_ring.sup_assoc BooleanRing.sup_assoc

theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  dsimp only [(· ⊓ ·)]
  -- ⊢ a * b * c = a * (b * c)
  ring
  -- 🎉 no goals
#align boolean_ring.inf_assoc BooleanRing.inf_assoc

theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  -- ⊢ a + a * b + a * (a * b) = a
  rw [← mul_assoc, mul_self, add_assoc, add_self, add_zero]
  -- 🎉 no goals
#align boolean_ring.sup_inf_self BooleanRing.sup_inf_self

theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  -- ⊢ a * (a + b + a * b) = a
  rw [mul_add, mul_add, mul_self, ← mul_assoc, mul_self, add_assoc, add_self, add_zero]
  -- 🎉 no goals
#align boolean_ring.inf_sup_self BooleanRing.inf_sup_self

theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) :=
      by ring
         -- 🎉 no goals
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]
                                      -- 🎉 no goals

#align boolean_ring.le_sup_inf_aux BooleanRing.le_sup_inf_aux

theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  -- ⊢ (a + b + a * b) * (a + c + a * c) + (a + b * c + a * (b * c)) + (a + b + a * …
  rw [le_sup_inf_aux, add_self, mul_self, zero_add]
  -- 🎉 no goals
#align boolean_ring.le_sup_inf BooleanRing.le_sup_inf

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
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, (add_comm a 1),
                                                     add_assoc, add_self, add_zero]
    bot := 0
    bot_le := fun a => show 0 + a + 0 * a = a by rw [zero_mul, zero_add, add_zero]
                                                 -- 🎉 no goals
    compl := fun a => 1 + a
    inf_compl_le_bot := fun a =>
                                                    -- 🎉 no goals
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by norm_num [mul_add, mul_self, add_self]
    top_le_sup_compl := fun a => by
      change
        1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) =
          a + (1 + a) + a * (1 + a)
      -- ⊢ 1 + (a + (1 + a)) = 0
      norm_num [mul_add, mul_self, add_self]
      -- 🎉 no goals
      rw [← add_assoc, add_self] }
#align boolean_ring.to_boolean_algebra BooleanRing.toBooleanAlgebra

-- Porting note: TODO: add priority 100. lower instance priority
scoped[BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.toBooleanAlgebra

end BooleanRing

instance : BooleanAlgebra (AsBoolAlg α) :=
  @BooleanRing.toBooleanAlgebra α _

@[simp]
theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 :=
  rfl
#align of_boolalg_top ofBoolAlg_top

@[simp]
theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 :=
  rfl
#align of_boolalg_bot ofBoolAlg_bot

@[simp]
theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b :=
  rfl
#align of_boolalg_sup ofBoolAlg_sup

@[simp]
theorem ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b :=
  rfl
#align of_boolalg_inf ofBoolAlg_inf

@[simp]
theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a :=
  rfl
#align of_boolalg_compl ofBoolAlg_compl

@[simp]
theorem ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b) :=
  rfl
#align of_boolalg_sdiff ofBoolAlg_sdiff

private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc
    (a + b + a * b) * (1 + a * b) = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) :=
      by ring
         -- 🎉 no goals
    _ = a + b := by simp only [mul_self, add_self, add_zero]
                    -- 🎉 no goals

@[simp]
theorem ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b := by
  rw [symmDiff_eq_sup_sdiff_inf]
  -- ⊢ ↑ofBoolAlg ((a ⊔ b) \ (a ⊓ b)) = ↑ofBoolAlg a + ↑ofBoolAlg b
  exact of_boolalg_symmDiff_aux _ _
  -- 🎉 no goals
#align of_boolalg_symm_diff ofBoolAlg_symmDiff

@[simp]
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} :
    ofBoolAlg a * ofBoolAlg b = ofBoolAlg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolAlg α) _ _ _
#align of_boolalg_mul_of_boolalg_eq_left_iff ofBoolAlg_mul_ofBoolAlg_eq_left_iff

@[simp]
theorem toBoolAlg_zero : toBoolAlg (0 : α) = ⊥ :=
  rfl
#align to_boolalg_zero toBoolAlg_zero

@[simp]
theorem toBoolAlg_one : toBoolAlg (1 : α) = ⊤ :=
  rfl
#align to_boolalg_one toBoolAlg_one

@[simp]
theorem toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b :=
  rfl
#align to_boolalg_mul toBoolAlg_mul

-- `toBoolAlg_add` simplifies the LHS but this lemma is eligible to `dsimp`
@[simp, nolint simpNF]
theorem toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b :=
  rfl
#align to_boolalg_add_add_mul toBoolAlg_add_add_mul

@[simp]
theorem toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b :=
  (ofBoolAlg_symmDiff _ _).symm
#align to_boolalg_add toBoolAlg_add

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
protected def RingHom.asBoolAlg (f : α →+* β) : BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β) where
  toFun := toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    -- ⊢ ↑toBoolAlg (↑f (↑ofBoolAlg a + ↑ofBoolAlg b + ↑ofBoolAlg a * ↑ofBoolAlg b))  …
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
    -- 🎉 no goals
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'
#align ring_hom.as_boolalg RingHom.asBoolAlg

@[simp]
theorem RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _ :=
  rfl
#align ring_hom.as_boolalg_id RingHom.asBoolAlg_id

@[simp]
theorem RingHom.asBoolAlg_comp (g : β →+* γ) (f : α →+* β) :
    (g.comp f).asBoolAlg = g.asBoolAlg.comp f.asBoolAlg :=
  rfl
#align ring_hom.as_boolalg_comp RingHom.asBoolAlg_comp

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolRing (α : Type*) :=
  α
#align as_boolring AsBoolRing

/-- The "identity" equivalence between `AsBoolRing α` and `α`. -/
def toBoolRing : α ≃ AsBoolRing α :=
  Equiv.refl _
#align to_boolring toBoolRing

/-- The "identity" equivalence between `α` and `AsBoolRing α`. -/
def ofBoolRing : AsBoolRing α ≃ α :=
  Equiv.refl _
#align of_boolring ofBoolRing

@[simp]
theorem toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing :=
  rfl
#align to_boolring_symm_eq toBoolRing_symm_eq

@[simp]
theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing :=
  rfl
#align of_boolring_symm_eq ofBoolRing_symm_eq

@[simp]
theorem toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a :=
  rfl
#align to_boolring_of_boolring toBoolRing_ofBoolRing

@[simp]
theorem ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a :=
  rfl
#align of_boolring_to_boolring ofBoolRing_toBoolRing

-- Porting note: simp can prove this -- @[simp]
theorem toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b :=
  Iff.rfl
#align to_boolring_inj toBoolRing_inj

-- Porting note: simp can prove this -- @[simp]
theorem ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b :=
  Iff.rfl
#align of_boolring_inj ofBoolRing_inj

instance [Inhabited α] : Inhabited (AsBoolRing α) :=
  ‹Inhabited α›

-- See note [reducible non-instances]
/-- Every generalized Boolean algebra has the structure of a non unital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
@[reducible]
def GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α] :
    NonUnitalCommRing α where
  add := (· ∆ ·)
  add_assoc := symmDiff_assoc
  zero := ⊥
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  zero_mul _ := bot_inf_eq
  mul_zero _ := inf_bot_eq
  neg := id
  add_left_neg := symmDiff_self
  add_comm := symmDiff_comm
  mul := (· ⊓ ·)
  mul_assoc _ _ _ := inf_assoc
  mul_comm _ _ := inf_comm
  left_distrib := inf_symmDiff_distrib_left
  right_distrib := inf_symmDiff_distrib_right
#align generalized_boolean_algebra.to_non_unital_comm_ring GeneralizedBooleanAlgebra.toNonUnitalCommRing

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
@[reducible]
def BooleanAlgebra.toBooleanRing : BooleanRing α :=
  { GeneralizedBooleanAlgebra.toNonUnitalCommRing with
    one := ⊤
    one_mul := fun _ => top_inf_eq
    mul_one := fun _ => inf_top_eq
    mul_self := fun b => inf_idem }
#align boolean_algebra.to_boolean_ring BooleanAlgebra.toBooleanRing

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

instance : BooleanRing (AsBoolRing α) :=
  @BooleanAlgebra.toBooleanRing α _

@[simp]
theorem ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥ :=
  rfl
#align of_boolring_zero ofBoolRing_zero

@[simp]
theorem ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤ :=
  rfl
#align of_boolring_one ofBoolRing_one

-- `sub_eq_add` proves this lemma but it is eligible for `dsimp`
@[simp, nolint simpNF]
theorem ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a :=
  rfl
#align of_boolring_neg ofBoolRing_neg

@[simp]
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl
#align of_boolring_add ofBoolRing_add

-- `sub_eq_add` simplifies the LHS but this lemma is eligible for `dsimp`
@[simp, nolint simpNF]
theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl
#align of_boolring_sub ofBoolRing_sub

@[simp]
theorem ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b :=
  rfl
#align of_boolring_mul ofBoolRing_mul

@[simp]
theorem ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} :
    ofBoolRing a ≤ ofBoolRing b ↔ a * b = a :=
  inf_eq_left.symm
#align of_boolring_le_of_boolring_iff ofBoolRing_le_ofBoolRing_iff

@[simp]
theorem toBoolRing_bot : toBoolRing (⊥ : α) = 0 :=
  rfl
#align to_boolring_bot toBoolRing_bot

@[simp]
theorem toBoolRing_top : toBoolRing (⊤ : α) = 1 :=
  rfl
#align to_boolring_top toBoolRing_top

@[simp]
theorem toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b :=
  rfl
#align to_boolring_inf toBoolRing_inf

@[simp]
theorem toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b :=
  rfl
#align to_boolring_symm_diff toBoolRing_symmDiff

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
#align bounded_lattice_hom.as_boolring BoundedLatticeHom.asBoolRing

@[simp]
theorem BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = RingHom.id _ :=
  rfl
#align bounded_lattice_hom.as_boolring_id BoundedLatticeHom.asBoolRing_id

@[simp]
theorem BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing :=
  rfl
#align bounded_lattice_hom.as_boolring_comp BoundedLatticeHom.asBoolRing_comp

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps!]
def OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (AsBoolRing α) ≃o α :=
  ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩
#align order_iso.as_boolalg_as_boolring OrderIso.asBoolAlgAsBoolRing

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps!]
def RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (AsBoolAlg α) ≃+* α :=
  { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }
#align ring_equiv.as_boolring_as_boolalg RingEquiv.asBoolRingAsBoolAlg

open Bool

instance : BooleanRing Bool where
  add := xor
  add_assoc := xor_assoc
  zero := false
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg := id
  sub := xor
  sub_eq_add_neg _ _ := rfl
  add_left_neg := Bool.xor_self
  add_comm := xor_comm
  one := true
  mul := and
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  mul_self := Bool.and_self
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl
                   -- ⊢ false * 0 = 0
                               -- 🎉 no goals
                               -- 🎉 no goals
