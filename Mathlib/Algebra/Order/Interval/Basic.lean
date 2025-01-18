/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Positivity.Core

/-!
# Interval arithmetic

This file defines arithmetic operations on intervals and prove their correctness. Note that this is
full precision operations. The essentials of float operations can be found
in `Data.FP.Basic`. We have not yet integrated these with the rest of the library.
-/


open Function Set

open scoped Pointwise

universe u

variable {ι α : Type*}

/-! ### One/zero -/


section One

section Preorder

variable [Preorder α] [One α]

@[to_additive]
instance : One (NonemptyInterval α) :=
  ⟨NonemptyInterval.pure 1⟩

namespace NonemptyInterval

@[to_additive (attr := simp) toProd_zero]
theorem toProd_one : (1 : NonemptyInterval α).toProd = 1 :=
  rfl

@[to_additive]
theorem fst_one : (1 : NonemptyInterval α).fst = 1 :=
  rfl

@[to_additive]
theorem snd_one : (1 : NonemptyInterval α).snd = 1 :=
  rfl

-- Porting note: Originally `@[simp, norm_cast, to_additive]`
@[to_additive (attr := push_cast, simp)]
theorem coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem pure_one : pure (1 : α) = 1 :=
  rfl

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
theorem pure_one : pure (1 : α) = 1 :=
  rfl

@[to_additive] lemma one_ne_bot : (1 : Interval α) ≠ ⊥ := pure_ne_bot

@[to_additive] lemma bot_ne_one : (⊥ : Interval α) ≠ 1 := bot_ne_pure

end Interval

end Preorder

section PartialOrder

variable [PartialOrder α] [One α]

namespace NonemptyInterval

@[to_additive (attr := simp)]
theorem coe_one : ((1 : NonemptyInterval α) : Set α) = 1 :=
  coe_pure _

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : NonemptyInterval α) :=
  ⟨le_rfl, le_rfl⟩

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
theorem coe_one : ((1 : Interval α) : Set α) = 1 :=
  Icc_self _

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Interval α) :=
  ⟨le_rfl, le_rfl⟩

end Interval

end PartialOrder

end One

/-!
### Addition/multiplication

Note that this multiplication does not apply to `ℚ` or `ℝ`.
-/


section Mul

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
instance : Mul (NonemptyInterval α) :=
  ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]
instance : Mul (Interval α) :=
  ⟨Option.map₂ (· * ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[to_additive (attr := simp) toProd_add]
theorem toProd_mul : (s * t).toProd = s.toProd * t.toProd :=
  rfl

@[to_additive]
theorem fst_mul : (s * t).fst = s.fst * t.fst :=
  rfl

@[to_additive]
theorem snd_mul : (s * t).snd = s.snd * t.snd :=
  rfl

@[to_additive (attr := simp)]
theorem coe_mul_interval : (↑(s * t) : Interval α) = s * t :=
  rfl

@[to_additive (attr := simp)]
theorem pure_mul_pure : pure a * pure b = pure (a * b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[to_additive (attr := simp)]
theorem bot_mul : ⊥ * t = ⊥ :=
  rfl

@[to_additive]
theorem mul_bot : s * ⊥ = ⊥ :=
  Option.map₂_none_right _ _

-- simp can already prove `add_bot`
attribute [simp] mul_bot

end Interval

end Mul

/-! ### Powers -/


-- TODO: if `to_additive` gets improved sufficiently, derive this from `hasPow`
instance NonemptyInterval.hasNSMul [AddMonoid α] [Preorder α] [AddLeftMono α]
    [AddRightMono α] : SMul ℕ (NonemptyInterval α) :=
  ⟨fun n s => ⟨(n • s.fst, n • s.snd), nsmul_le_nsmul_right s.fst_le_snd _⟩⟩

section Pow

variable [Monoid α] [Preorder α]

@[to_additive existing]
instance NonemptyInterval.hasPow [MulLeftMono α] [MulRightMono α] :
    Pow (NonemptyInterval α) ℕ :=
  ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

namespace NonemptyInterval

variable [MulLeftMono α] [MulRightMono α]
variable (s : NonemptyInterval α) (a : α) (n : ℕ)

@[to_additive (attr := simp) toProd_nsmul]
theorem toProd_pow : (s ^ n).toProd = s.toProd ^ n :=
  rfl

@[to_additive]
theorem fst_pow : (s ^ n).fst = s.fst ^ n :=
  rfl

@[to_additive]
theorem snd_pow : (s ^ n).snd = s.snd ^ n :=
  rfl

@[to_additive (attr := simp)]
theorem pure_pow : pure a ^ n = pure (a ^ n) :=
  rfl

end NonemptyInterval

end Pow

namespace NonemptyInterval

@[to_additive]
instance commMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    CommMonoid (NonemptyInterval α) :=
  NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

end NonemptyInterval

@[to_additive]
instance Interval.mulOneClass [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    MulOneClass (Interval α) where
  mul := (· * ·)
  one := 1
  one_mul s :=
    (Option.map₂_coe_left _ _ _).trans <| by
      simp_rw [one_mul, ← Function.id_def, Option.map_id, id]
  mul_one s :=
    (Option.map₂_coe_right _ _ _).trans <| by
      simp_rw [mul_one, ← Function.id_def, Option.map_id, id]

@[to_additive]
instance Interval.commMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    CommMonoid (Interval α) :=
  { Interval.mulOneClass with
    mul_comm := fun _ _ => Option.map₂_comm mul_comm
    mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc }

namespace NonemptyInterval

@[to_additive]
theorem coe_pow_interval [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    (s : NonemptyInterval α) (n : ℕ) :
    ↑(s ^ n) = (s : Interval α) ^ n :=
  map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α →* Interval α) _ _

-- simp can already prove `coe_nsmul_interval`
attribute [simp] coe_pow_interval

end NonemptyInterval

namespace Interval

variable [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] (s : Interval α) {n : ℕ}

@[to_additive]
theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Interval α) ^ n = ⊥
  | 0, h => (h rfl).elim
  | Nat.succ n, _ => mul_bot (⊥ ^ n)

end Interval

/-!
### Semiring structure

When `α` is a canonically `OrderedCommSemiring`, the previous `+` and `*` on `NonemptyInterval α`
form a `CommSemiring`.
-/

section NatCast
variable [Preorder α] [NatCast α]

namespace NonemptyInterval

instance : NatCast (NonemptyInterval α) where
  natCast n := pure <| Nat.cast n

theorem fst_natCast (n : ℕ) : (n : NonemptyInterval α).fst = n := rfl

theorem snd_natCast (n : ℕ) : (n : NonemptyInterval α).snd = n := rfl

@[simp]
theorem pure_natCast (n : ℕ) : pure (n : α) = n := rfl

end NonemptyInterval

end NatCast

namespace NonemptyInterval

instance [OrderedCommSemiring α] [CanonicallyOrderedAdd α] : CommSemiring (NonemptyInterval α) :=
  NonemptyInterval.toProd_injective.commSemiring _
    toProd_zero toProd_one toProd_add toProd_mul (swap toProd_nsmul) toProd_pow (fun _ => rfl)

end NonemptyInterval

/-!
### Subtraction

Subtraction is defined more generally than division so that it applies to `ℕ` (and `OrderedDiv`
is not a thing and probably should not become one).
-/


section Sub

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

instance : Sub (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

instance : Sub (Interval α) :=
  ⟨Option.map₂ Sub.sub⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) {a b : α}

@[simp]
theorem fst_sub : (s - t).fst = s.fst - t.snd :=
  rfl

@[simp]
theorem snd_sub : (s - t).snd = s.snd - t.fst :=
  rfl

@[simp]
theorem coe_sub_interval : (↑(s - t) : Interval α) = s - t :=
  rfl

theorem sub_mem_sub (ha : a ∈ s) (hb : b ∈ t) : a - b ∈ s - t :=
  ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

@[simp]
theorem pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[simp]
theorem bot_sub : ⊥ - t = ⊥ :=
  rfl

@[simp]
theorem sub_bot : s - ⊥ = ⊥ :=
  Option.map₂_none_right _ _

end Interval

end Sub

/-!
### Division in ordered groups

Note that this division does not apply to `ℚ` or `ℝ`.
-/


section Div

variable [Preorder α] [CommGroup α] [MulLeftMono α]

@[to_additive existing]
instance : Div (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive existing]
instance : Div (Interval α) :=
  ⟨Option.map₂ (· / ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[to_additive existing (attr := simp)]
theorem fst_div : (s / t).fst = s.fst / t.snd :=
  rfl

@[to_additive existing (attr := simp)]
theorem snd_div : (s / t).snd = s.snd / t.fst :=
  rfl

@[to_additive existing (attr := simp)]
theorem coe_div_interval : (↑(s / t) : Interval α) = s / t :=
  rfl

@[to_additive existing]
theorem div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t :=
  ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

@[to_additive existing (attr := simp)]
theorem pure_div_pure : pure a / pure b = pure (a / b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[to_additive existing (attr := simp)]
theorem bot_div : ⊥ / t = ⊥ :=
  rfl

@[to_additive existing (attr := simp)]
theorem div_bot : s / ⊥ = ⊥ :=
  Option.map₂_none_right _ _

end Interval

end Div

/-! ### Negation/inversion -/


section Inv

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

@[to_additive]
instance : Inv (NonemptyInterval α) :=
  ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]
instance : Inv (Interval α) :=
  ⟨Option.map Inv.inv⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

@[to_additive (attr := simp)]
theorem fst_inv : s⁻¹.fst = s.snd⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem snd_inv : s⁻¹.snd = s.fst⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹ :=
  rfl

@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

@[to_additive (attr := simp)]
theorem inv_pure : (pure a)⁻¹ = pure a⁻¹ :=
  rfl

end NonemptyInterval

@[to_additive (attr := simp)]
theorem Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥ :=
  rfl

end Inv

namespace NonemptyInterval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : NonemptyInterval α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure, h, pure_one]

instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (NonemptyInterval α) :=
  { NonemptyInterval.addCommMonoid with
    neg := Neg.neg
    sub := Sub.sub
    sub_eq_add_neg := fun s t => by
      refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
      exact sub_eq_add_neg _ _
    neg_neg := fun s => by apply NonemptyInterval.ext; exact neg_neg _
    neg_add_rev := fun s t => by
      refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
      exact neg_add_rev _ _
    neg_eq_of_add := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.add_eq_zero_iff.1 h
      rw [neg_pure, neg_eq_of_add_eq_zero_right hab]
    -- TODO: use a better defeq
    zsmul := zsmulRec }

@[to_additive existing NonemptyInterval.subtractionCommMonoid]
instance divisionCommMonoid : DivisionCommMonoid (NonemptyInterval α) :=
  { NonemptyInterval.commMonoid with
    inv := Inv.inv
    div := (· / ·)
    div_eq_mul_inv := fun s t => by
      refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
      exact div_eq_mul_inv _ _
    inv_inv := fun s => by apply NonemptyInterval.ext; exact inv_inv _
    mul_inv_rev := fun s t => by
      refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
      exact mul_inv_rev _ _
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.mul_eq_one_iff.1 h
      rw [inv_pure, inv_eq_of_mul_eq_one_right hab] }

end NonemptyInterval

namespace Interval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : Interval α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      WithBot.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (Interval α) :=
  { Interval.addCommMonoid with
    neg := Neg.neg
    sub := Sub.sub
    sub_eq_add_neg := by
      rintro (_ | s) (_ | t) <;> first |rfl|exact congr_arg some (sub_eq_add_neg _ _)
    neg_neg := by rintro (_ | s) <;> first |rfl|exact congr_arg some (neg_neg _)
    neg_add_rev := by rintro (_ | s) (_ | t) <;> first |rfl|exact congr_arg some (neg_add_rev _ _)
    neg_eq_of_add := by
      rintro (_ | s) (_ | t) h <;>
        first
          | cases h
          | exact congr_arg some (neg_eq_of_add_eq_zero_right <| Option.some_injective _ h)
    -- TODO: use a better defeq
    zsmul := zsmulRec }

@[to_additive existing Interval.subtractionCommMonoid]
instance divisionCommMonoid : DivisionCommMonoid (Interval α) :=
  { Interval.commMonoid with
    inv := Inv.inv
    div := (· / ·)
    div_eq_mul_inv := by
      rintro (_ | s) (_ | t) <;> first |rfl|exact congr_arg some (div_eq_mul_inv _ _)
    inv_inv := by rintro (_ | s) <;> first |rfl|exact congr_arg some (inv_inv _)
    mul_inv_rev := by rintro (_ | s) (_ | t) <;> first |rfl|exact congr_arg some (mul_inv_rev _ _)
    inv_eq_of_mul := by
      rintro (_ | s) (_ | t) h <;>
        first
          | cases h
          | exact congr_arg some (inv_eq_of_mul_eq_one_right <| Option.some_injective _ h) }

end Interval

section Length

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : α :=
  s.snd - s.fst

@[simp]
theorem length_nonneg : 0 ≤ s.length :=
  sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
@[simp]
theorem length_pure : (pure a).length = 0 :=
  sub_self _

omit [IsOrderedAddMonoid α] in
@[simp]
theorem length_zero : (0 : NonemptyInterval α).length = 0 :=
  length_pure _

@[simp]
theorem length_neg : (-s).length = s.length :=
  neg_sub_neg _ _

@[simp]
theorem length_add : (s + t).length = s.length + t.length :=
  add_sub_add_comm _ _ _ _

@[simp]
theorem length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]

@[simp]
theorem length_sum (f : ι → NonemptyInterval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length :=
  map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α →+ α) _ _

end NonemptyInterval

namespace Interval

variable (s t : Interval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : Interval α → α
  | ⊥ => 0
  | (s : NonemptyInterval α) => s.length

@[simp]
theorem length_nonneg : ∀ s : Interval α, 0 ≤ s.length
  | ⊥ => le_rfl
  | (s : NonemptyInterval α) => s.length_nonneg

omit [IsOrderedAddMonoid α] in
@[simp]
theorem length_pure : (pure a).length = 0 :=
  NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
@[simp]
theorem length_zero : (0 : Interval α).length = 0 :=
  length_pure _

@[simp]
theorem length_neg : ∀ s : Interval α, (-s).length = s.length
  | ⊥ => rfl
  | (s : NonemptyInterval α) => s.length_neg

theorem length_add_le : ∀ s t : Interval α, (s + t).length ≤ s.length + t.length
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => (s.length_add t).le

theorem length_sub_le : (s - t).length ≤ s.length + t.length := by
  simpa [sub_eq_add_neg] using length_add_le s (-t)

theorem length_sum_le (f : ι → Interval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length ≤ ∑ i ∈ s, (f i).length :=
  Finset.le_sum_of_subadditive _ length_zero length_add_le _ _

end Interval

end Length

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity NonemptyInterval.length _]
def evalNonemptyIntervalLength : PositivityExt where
  eval {u α} _ _ e := do
    let ~q(@NonemptyInterval.length _ $ig $ipo $a) := e |
      throwError "not NonemptyInterval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assertInstancesCommute
    return .nonnegative q(NonemptyInterval.length_nonneg $a)

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity Interval.length _]
def evalIntervalLength : PositivityExt where
  eval {u α} _ _ e := do
    let ~q(@Interval.length _ $ig $ipo $a) := e | throwError "not Interval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assumeInstancesCommute
    return .nonnegative q(Interval.length_nonneg $a)

end Mathlib.Meta.Positivity
