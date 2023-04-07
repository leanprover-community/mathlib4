/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies

! This file was ported from Lean 3 source module algebra.ring.boolean_ring
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.PunitInstances
import Mathbin.Tactic.Abel
import Mathbin.Tactic.Ring
import Mathbin.Order.Hom.Lattice

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: Turn a Boolean ring into a Boolean algebra.
* `boolean_algebra.to_boolean_ring`: Turn a Boolean algebra into a Boolean ring.
* `as_boolalg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `as_boolring`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `boolean_algebra_of_boolean_ring` and
  `boolean_ring_of_boolean_algebra`.
* Type-synonyms `as_boolalg` and `as_boolring`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`of_boolalg`/`to_boolalg`/`of_boolring`/`to_boolring` explicitly.

## Tags

boolean ring, boolean algebra
-/


variable {α β γ : Type _}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ring α where
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
theorem add_self : a + a = 0 :=
  by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
      
  rwa [self_eq_add_left] at this
#align add_self add_self

@[simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_self, add_assoc]
    _ = a := by rw [add_self, zero_add]
    
#align neg_eq neg_eq

theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]
    
#align add_eq_zero' add_eq_zero'

@[simp]
theorem mul_add_mul : a * b + b * a = 0 :=
  by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
      
  rwa [self_eq_add_right] at this
#align mul_add_mul mul_add_mul

@[simp]
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]
#align sub_eq_add sub_eq_add

@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]
#align mul_one_add_self mul_one_add_self

-- Note [lower instance priority]
instance (priority := 100) BooleanRing.toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }
#align boolean_ring.to_comm_ring BooleanRing.toCommRing

end BooleanRing

instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolalg (α : Type _) :=
  α
#align as_boolalg AsBoolalg

/-- The "identity" equivalence between `as_boolalg α` and `α`. -/
def toBoolalg : α ≃ AsBoolalg α :=
  Equiv.refl _
#align to_boolalg toBoolalg

/-- The "identity" equivalence between `α` and `as_boolalg α`. -/
def ofBoolalg : AsBoolalg α ≃ α :=
  Equiv.refl _
#align of_boolalg ofBoolalg

@[simp]
theorem toBoolalg_symm_eq : (@toBoolalg α).symm = ofBoolalg :=
  rfl
#align to_boolalg_symm_eq toBoolalg_symm_eq

@[simp]
theorem ofBoolalg_symm_eq : (@ofBoolalg α).symm = toBoolalg :=
  rfl
#align of_boolalg_symm_eq ofBoolalg_symm_eq

@[simp]
theorem toBoolalg_ofBoolalg (a : AsBoolalg α) : toBoolalg (ofBoolalg a) = a :=
  rfl
#align to_boolalg_of_boolalg toBoolalg_ofBoolalg

@[simp]
theorem ofBoolalg_toBoolalg (a : α) : ofBoolalg (toBoolalg a) = a :=
  rfl
#align of_boolalg_to_boolalg ofBoolalg_toBoolalg

@[simp]
theorem toBoolalg_inj {a b : α} : toBoolalg a = toBoolalg b ↔ a = b :=
  Iff.rfl
#align to_boolalg_inj toBoolalg_inj

@[simp]
theorem ofBoolalg_inj {a b : AsBoolalg α} : ofBoolalg a = ofBoolalg b ↔ a = b :=
  Iff.rfl
#align of_boolalg_inj ofBoolalg_inj

instance [Inhabited α] : Inhabited (AsBoolalg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
def hasSup : Sup α :=
  ⟨fun x y => x + y + x * y⟩
#align boolean_ring.has_sup BooleanRing.hasSup

/-- The meet operation in a Boolean ring is `x * y`. -/
def hasInf : Inf α :=
  ⟨(· * ·)⟩
#align boolean_ring.has_inf BooleanRing.hasInf

scoped[-- Note [lower instance priority]
BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasSup

scoped[BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasInf

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a :=
  by
  dsimp only [(· ⊔ ·)]
  ring
#align boolean_ring.sup_comm BooleanRing.sup_comm

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a :=
  by
  dsimp only [(· ⊓ ·)]
  ring
#align boolean_ring.inf_comm BooleanRing.inf_comm

theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  by
  dsimp only [(· ⊔ ·)]
  ring
#align boolean_ring.sup_assoc BooleanRing.sup_assoc

theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  by
  dsimp only [(· ⊓ ·)]
  ring
#align boolean_ring.inf_assoc BooleanRing.inf_assoc

theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a :=
  by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  assoc_rw [mul_self, add_self, add_zero]
#align boolean_ring.sup_inf_self BooleanRing.sup_inf_self

theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a :=
  by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add, mul_add, mul_self, ← mul_assoc, mul_self, add_assoc, add_self, add_zero]
#align boolean_ring.inf_sup_self BooleanRing.inf_sup_self

theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) :=
      by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]
    
#align boolean_ring.le_sup_inf_aux BooleanRing.le_sup_inf_aux

theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c :=
  by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_add]
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
  {
    Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self
      inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by assoc_rw [mul_one, add_comm, add_self, add_zero]
    bot := 0
    bot_le := fun a => show 0 + a + 0 * a = a by rw [MulZeroClass.zero_mul, zero_add, add_zero]
    compl := fun a => 1 + a
    inf_compl_le_bot := fun a =>
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by norm_num [mul_add, mul_self, add_self]
    top_le_sup_compl := fun a =>
      by
      change
        1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) =
          a + (1 + a) + a * (1 + a)
      norm_num [mul_add, mul_self]
      rw [← add_assoc, add_self] }
#align boolean_ring.to_boolean_algebra BooleanRing.toBooleanAlgebra

scoped[BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.toBooleanAlgebra

end BooleanRing

instance : BooleanAlgebra (AsBoolalg α) :=
  @BooleanRing.toBooleanAlgebra α _

@[simp]
theorem ofBoolalg_top : ofBoolalg (⊤ : AsBoolalg α) = 1 :=
  rfl
#align of_boolalg_top ofBoolalg_top

@[simp]
theorem ofBoolalg_bot : ofBoolalg (⊥ : AsBoolalg α) = 0 :=
  rfl
#align of_boolalg_bot ofBoolalg_bot

@[simp]
theorem ofBoolalg_sup (a b : AsBoolalg α) :
    ofBoolalg (a ⊔ b) = ofBoolalg a + ofBoolalg b + ofBoolalg a * ofBoolalg b :=
  rfl
#align of_boolalg_sup ofBoolalg_sup

@[simp]
theorem ofBoolalg_inf (a b : AsBoolalg α) : ofBoolalg (a ⊓ b) = ofBoolalg a * ofBoolalg b :=
  rfl
#align of_boolalg_inf ofBoolalg_inf

@[simp]
theorem ofBoolalg_compl (a : AsBoolalg α) : ofBoolalg (aᶜ) = 1 + ofBoolalg a :=
  rfl
#align of_boolalg_compl ofBoolalg_compl

@[simp]
theorem ofBoolalg_sdiff (a b : AsBoolalg α) : ofBoolalg (a \ b) = ofBoolalg a * (1 + ofBoolalg b) :=
  rfl
#align of_boolalg_sdiff ofBoolalg_sdiff

private theorem of_boolalg_symm_diff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc
    (a + b + a * b) * (1 + a * b) = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) :=
      by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]
    
#align of_boolalg_symm_diff_aux of_boolalg_symm_diff_aux

@[simp]
theorem ofBoolalg_symmDiff (a b : AsBoolalg α) : ofBoolalg (a ∆ b) = ofBoolalg a + ofBoolalg b :=
  by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symm_diff_aux _ _
#align of_boolalg_symm_diff ofBoolalg_symmDiff

@[simp]
theorem ofBoolalg_mul_ofBoolalg_eq_left_iff {a b : AsBoolalg α} :
    ofBoolalg a * ofBoolalg b = ofBoolalg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolalg α) _ _ _
#align of_boolalg_mul_of_boolalg_eq_left_iff ofBoolalg_mul_ofBoolalg_eq_left_iff

@[simp]
theorem toBoolalg_zero : toBoolalg (0 : α) = ⊥ :=
  rfl
#align to_boolalg_zero toBoolalg_zero

@[simp]
theorem toBoolalg_one : toBoolalg (1 : α) = ⊤ :=
  rfl
#align to_boolalg_one toBoolalg_one

@[simp]
theorem toBoolalg_mul (a b : α) : toBoolalg (a * b) = toBoolalg a ⊓ toBoolalg b :=
  rfl
#align to_boolalg_mul toBoolalg_mul

-- `to_boolalg_add` simplifies the LHS but this lemma is eligible to `dsimp`
@[simp, nolint simp_nf]
theorem toBoolalg_add_add_mul (a b : α) : toBoolalg (a + b + a * b) = toBoolalg a ⊔ toBoolalg b :=
  rfl
#align to_boolalg_add_add_mul toBoolalg_add_add_mul

@[simp]
theorem toBoolalg_add (a b : α) : toBoolalg (a + b) = toBoolalg a ∆ toBoolalg b :=
  (ofBoolalg_symmDiff _ _).symm
#align to_boolalg_add toBoolalg_add

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
protected def RingHom.asBoolalg (f : α →+* β) : BoundedLatticeHom (AsBoolalg α) (AsBoolalg β)
    where
  toFun := toBoolalg ∘ f ∘ ofBoolalg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f]
    rfl
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'
#align ring_hom.as_boolalg RingHom.asBoolalg

@[simp]
theorem RingHom.asBoolalg_id : (RingHom.id α).AsBoolalg = BoundedLatticeHom.id _ :=
  rfl
#align ring_hom.as_boolalg_id RingHom.asBoolalg_id

@[simp]
theorem RingHom.asBoolalg_comp (g : β →+* γ) (f : α →+* β) :
    (g.comp f).AsBoolalg = g.AsBoolalg.comp f.AsBoolalg :=
  rfl
#align ring_hom.as_boolalg_comp RingHom.asBoolalg_comp

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolring (α : Type _) :=
  α
#align as_boolring AsBoolring

/-- The "identity" equivalence between `as_boolring α` and `α`. -/
def toBoolring : α ≃ AsBoolring α :=
  Equiv.refl _
#align to_boolring toBoolring

/-- The "identity" equivalence between `α` and `as_boolring α`. -/
def ofBoolring : AsBoolring α ≃ α :=
  Equiv.refl _
#align of_boolring ofBoolring

@[simp]
theorem toBoolring_symm_eq : (@toBoolring α).symm = ofBoolring :=
  rfl
#align to_boolring_symm_eq toBoolring_symm_eq

@[simp]
theorem ofBoolring_symm_eq : (@ofBoolring α).symm = toBoolring :=
  rfl
#align of_boolring_symm_eq ofBoolring_symm_eq

@[simp]
theorem toBoolring_ofBoolring (a : AsBoolring α) : toBoolring (ofBoolring a) = a :=
  rfl
#align to_boolring_of_boolring toBoolring_ofBoolring

@[simp]
theorem ofBoolring_toBoolring (a : α) : ofBoolring (toBoolring a) = a :=
  rfl
#align of_boolring_to_boolring ofBoolring_toBoolring

@[simp]
theorem toBoolring_inj {a b : α} : toBoolring a = toBoolring b ↔ a = b :=
  Iff.rfl
#align to_boolring_inj toBoolring_inj

@[simp]
theorem ofBoolring_inj {a b : AsBoolring α} : ofBoolring a = ofBoolring b ↔ a = b :=
  Iff.rfl
#align of_boolring_inj ofBoolring_inj

instance [Inhabited α] : Inhabited (AsBoolring α) :=
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

instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolring α) :=
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
  {
    GeneralizedBooleanAlgebra.toNonUnitalCommRing with
    one := ⊤
    one_mul := fun _ => top_inf_eq
    mul_one := fun _ => inf_top_eq
    mul_self := fun b => inf_idem }
#align boolean_algebra.to_boolean_ring BooleanAlgebra.toBooleanRing

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

instance : BooleanRing (AsBoolring α) :=
  @BooleanAlgebra.toBooleanRing α _

@[simp]
theorem ofBoolring_zero : ofBoolring (0 : AsBoolring α) = ⊥ :=
  rfl
#align of_boolring_zero ofBoolring_zero

@[simp]
theorem ofBoolring_one : ofBoolring (1 : AsBoolring α) = ⊤ :=
  rfl
#align of_boolring_one ofBoolring_one

-- `sub_eq_add` proves this lemma but it is eligible for `dsimp`
@[simp, nolint simp_nf]
theorem ofBoolring_neg (a : AsBoolring α) : ofBoolring (-a) = ofBoolring a :=
  rfl
#align of_boolring_neg ofBoolring_neg

@[simp]
theorem ofBoolring_add (a b : AsBoolring α) : ofBoolring (a + b) = ofBoolring a ∆ ofBoolring b :=
  rfl
#align of_boolring_add ofBoolring_add

-- `sub_eq_add` simplifies the LHS but this lemma is eligible for `dsimp`
@[simp, nolint simp_nf]
theorem ofBoolring_sub (a b : AsBoolring α) : ofBoolring (a - b) = ofBoolring a ∆ ofBoolring b :=
  rfl
#align of_boolring_sub ofBoolring_sub

@[simp]
theorem ofBoolring_mul (a b : AsBoolring α) : ofBoolring (a * b) = ofBoolring a ⊓ ofBoolring b :=
  rfl
#align of_boolring_mul ofBoolring_mul

@[simp]
theorem ofBoolring_le_ofBoolring_iff {a b : AsBoolring α} :
    ofBoolring a ≤ ofBoolring b ↔ a * b = a :=
  inf_eq_left.symm
#align of_boolring_le_of_boolring_iff ofBoolring_le_ofBoolring_iff

@[simp]
theorem toBoolring_bot : toBoolring (⊥ : α) = 0 :=
  rfl
#align to_boolring_bot toBoolring_bot

@[simp]
theorem toBoolring_top : toBoolring (⊤ : α) = 1 :=
  rfl
#align to_boolring_top toBoolring_top

@[simp]
theorem toBoolring_inf (a b : α) : toBoolring (a ⊓ b) = toBoolring a * toBoolring b :=
  rfl
#align to_boolring_inf toBoolring_inf

@[simp]
theorem toBoolring_symmDiff (a b : α) : toBoolring (a ∆ b) = toBoolring a + toBoolring b :=
  rfl
#align to_boolring_symm_diff toBoolring_symmDiff

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
protected def BoundedLatticeHom.asBoolring (f : BoundedLatticeHom α β) :
    AsBoolring α →+* AsBoolring β
    where
  toFun := toBoolring ∘ f ∘ ofBoolring
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symm_diff' f
  map_mul' := f.map_inf'
#align bounded_lattice_hom.as_boolring BoundedLatticeHom.asBoolring

@[simp]
theorem BoundedLatticeHom.asBoolring_id : (BoundedLatticeHom.id α).AsBoolring = RingHom.id _ :=
  rfl
#align bounded_lattice_hom.as_boolring_id BoundedLatticeHom.asBoolring_id

@[simp]
theorem BoundedLatticeHom.asBoolring_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).AsBoolring = g.AsBoolring.comp f.AsBoolring :=
  rfl
#align bounded_lattice_hom.as_boolring_comp BoundedLatticeHom.asBoolring_comp

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps]
def OrderIso.asBoolalgAsBoolring (α : Type _) [BooleanAlgebra α] : AsBoolalg (AsBoolring α) ≃o α :=
  ⟨ofBoolalg.trans ofBoolring, fun a b =>
    ofBoolring_le_ofBoolring_iff.trans ofBoolalg_mul_ofBoolalg_eq_left_iff⟩
#align order_iso.as_boolalg_as_boolring OrderIso.asBoolalgAsBoolring

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps]
def RingEquiv.asBoolringAsBoolalg (α : Type _) [BooleanRing α] : AsBoolring (AsBoolalg α) ≃+* α :=
  { ofBoolring.trans ofBoolalg with
    map_mul' := fun a b => rfl
    map_add' := ofBoolalg_symmDiff }
#align ring_equiv.as_boolring_as_boolalg RingEquiv.asBoolringAsBoolalg

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

