/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Order.BoundedOrder.Basic

/-! # Ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

instance [LE α] : LE (Multiplicative α) :=
  inferInstanceAs <| LE α

instance [LE α] : LE (Additive α) :=
  inferInstanceAs <| LE α

instance [LT α] : LT (Multiplicative α) :=
  inferInstanceAs <| LT α

instance [LT α] : LT (Additive α) :=
  inferInstanceAs <| LT α

instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=
  inferInstanceAs <| Preorder α

instance Additive.preorder [Preorder α] : Preorder (Additive α) :=
  inferInstanceAs <| Preorder α

instance Multiplicative.partialOrder [PartialOrder α] : PartialOrder (Multiplicative α) :=
  inferInstanceAs <| PartialOrder α

instance Additive.partialOrder [PartialOrder α] : PartialOrder (Additive α) :=
  inferInstanceAs <| PartialOrder α

instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=
  inferInstanceAs <| LinearOrder α

instance Additive.linearOrder [LinearOrder α] : LinearOrder (Additive α) :=
  inferInstanceAs <| LinearOrder α

instance Multiplicative.orderBot [LE α] [OrderBot α] : OrderBot (Multiplicative α) :=
  inferInstanceAs <| OrderBot α

instance Additive.orderBot [LE α] [OrderBot α] : OrderBot (Additive α) :=
  inferInstanceAs <| OrderBot α

instance Multiplicative.orderTop [LE α] [OrderTop α] : OrderTop (Multiplicative α) :=
  inferInstanceAs <| OrderTop α

instance Additive.orderTop [LE α] [OrderTop α] : OrderTop (Additive α) :=
  inferInstanceAs <| OrderTop α

instance Multiplicative.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Multiplicative α) :=
  inferInstanceAs <| BoundedOrder α

instance Additive.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Additive α) :=
  inferInstanceAs <| BoundedOrder α

instance Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] :
    ExistsMulOfLE (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

instance Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

namespace Additive
section Preorder
variable [Preorder α]

@[simp]
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl

@[simp]
theorem toMul_le {a b : Additive α} : a.toMul ≤ b.toMul ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem toMul_lt {a b : Additive α} : a.toMul < b.toMul ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toMul_mono⟩ := toMul_le
@[gcongr] alias ⟨_, ofMul_mono⟩ := ofMul_le
@[gcongr] alias ⟨_, toMul_strictMono⟩ := toMul_lt
@[gcongr] alias ⟨_, ofMul_strictMono⟩ := ofMul_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

@[simp] lemma ofMul_top : ofMul (⊤ : α) = ⊤ := rfl
@[simp] lemma toMul_top : toMul ⊤ = (⊤ : α) := rfl

@[simp] lemma ofMul_eq_top {a : α} : ofMul a = ⊤ ↔ a = ⊤ := .rfl
@[simp] lemma toMul_eq_top {a : Additive α} : toMul a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

@[simp] lemma ofMul_bot : ofMul (⊥ : α) = ⊥ := rfl
@[simp] lemma toMul_bot : toMul ⊥ = (⊥ : α) := rfl

@[simp] lemma ofMul_eq_bot {a : α} : ofMul a = ⊥ ↔ a = ⊥ := .rfl
@[simp] lemma toMul_eq_bot {a : Additive α} : toMul a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot
end Additive

namespace Multiplicative
section Preorder
variable [Preorder α]

@[simp]
theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl

@[simp]
theorem toAdd_le {a b : Multiplicative α} : a.toAdd ≤ b.toAdd ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem toAdd_lt {a b : Multiplicative α} : a.toAdd < b.toAdd ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toAdd_mono⟩ := toAdd_le
@[gcongr] alias ⟨_, ofAdd_mono⟩ := ofAdd_le
@[gcongr] alias ⟨_, toAdd_strictMono⟩ := toAdd_lt
@[gcongr] alias ⟨_, ofAdd_strictMono⟩ := ofAdd_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

@[simp] lemma ofAdd_top : ofAdd (⊤ : α) = ⊤ := rfl
@[simp] lemma toAdd_top : toAdd ⊤ = (⊤ : α) := rfl

@[simp] lemma ofAdd_eq_top {a : α} : ofAdd a = ⊤ ↔ a = ⊤ := .rfl
@[simp] lemma toAdd_eq_top {a : Multiplicative α} : toAdd a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

@[simp] lemma ofAdd_bot : ofAdd (⊥ : α) = ⊥ := rfl
@[simp] lemma toAdd_bot : toAdd ⊥ = (⊥ : α) := rfl

@[simp] lemma ofAdd_eq_bot {a : α} : ofAdd a = ⊥ ↔ a = ⊥ := .rfl
@[simp] lemma toAdd_eq_bot {a : Multiplicative α} : toAdd a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot

end Multiplicative
