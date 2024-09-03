/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Classes.Order
import Mathlib.Init.Logic
import Mathlib.Data.Ordering.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

/-! ### Unbundled classes -/

universe u
variable {α : Type u}

/-- `IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
class IsIrrefl (α : Sort*) (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a

/-- `IsRefl X r` means the binary relation `r` on `X` is reflexive. -/
class IsRefl (α : Sort*) (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a

/-- `IsSymm X r` means the binary relation `r` on `X` is symmetric. -/
class IsSymm (α : Sort*) (r : α → α → Prop) : Prop where
  symm : ∀ a b, r a b → r b a

/-- `IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
class IsAsymm (α : Sort*) (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬r b a

/-- `IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
class IsAntisymm (α : Sort*) (r : α → α → Prop) : Prop where
  antisymm : ∀ a b, r a b → r b a → a = b

instance (priority := 100) IsAsymm.toIsAntisymm {α : Sort*} (r : α → α → Prop) [IsAsymm α r] :
    IsAntisymm α r where
  antisymm _ _ hx hy := (IsAsymm.asymm _ _ hx hy).elim

/-- `IsTrans X r` means the binary relation `r` on `X` is transitive. -/
class IsTrans (α : Sort*) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c

instance {α : Sort*} {r : α → α → Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩

instance (priority := 100) {α : Sort*} {r : α → α → Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩

/-- `IsTotal X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
class IsTotal (α : Sort*) (r : α → α → Prop) : Prop where
  total : ∀ a b, r a b ∨ r b a

/-- `IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class IsPreorder (α : Sort*) (r : α → α → Prop) extends IsRefl α r, IsTrans α r : Prop

/-- `IsPartialOrder X r` means that the binary relation `r` on `X` is a partial order, that is,
`IsPreorder X r` and `IsAntisymm X r`. -/
class IsPartialOrder (α : Sort*) (r : α → α → Prop) extends IsPreorder α r, IsAntisymm α r : Prop

/-- `IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order, that is,
`IsPartialOrder X r` and `IsTotal X r`. -/
class IsLinearOrder (α : Sort u) (r : α → α → Prop) extends IsPartialOrder α r, IsTotal α r : Prop

/-- `IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `IsPreorder X r` and `IsSymm X r`. -/
class IsEquiv (α : Sort*) (r : α → α → Prop) extends IsPreorder α r, IsSymm α r : Prop

/-- `IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order, that is,
`IsIrrefl X r` and `IsTrans X r`. -/
class IsStrictOrder (α : Sort*) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r : Prop

/-- `IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `IsStrictOrder X lt` and `¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a`. -/
class IsStrictWeakOrder (α : Sort u) (lt : α → α → Prop) extends IsStrictOrder α lt : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
class IsTrichotomous (α : Sort*) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a

/-- `IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `IsTrichotomous X lt` and `IsStrictOrder X lt`. -/
class IsStrictTotalOrder (α : Sort*) (lt : α → α → Prop) extends IsTrichotomous α lt,
    IsStrictOrder α lt : Prop

/-- Equality is an equivalence relation. -/
instance eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

section

variable {α : Sort*} {r : α → α → Prop} {a b c : α}

local infixl:50 " ≺ " => r

lemma irrefl [IsIrrefl α r] (a : α) : ¬a ≺ a := IsIrrefl.irrefl a
lemma refl [IsRefl α r] (a : α) : a ≺ a := IsRefl.refl a
lemma trans [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
lemma symm [IsSymm α r] : a ≺ b → b ≺ a := IsSymm.symm _ _
lemma antisymm [IsAntisymm α r] : a ≺ b → b ≺ a → a = b := IsAntisymm.antisymm _ _
lemma asymm [IsAsymm α r] : a ≺ b → ¬b ≺ a := IsAsymm.asymm _ _

lemma trichotomous [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  IsTrichotomous.trichotomous

instance (priority := 90) isAsymm_of_isTrans_of_isIrrefl [IsTrans α r] [IsIrrefl α r] :
    IsAsymm α r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩

variable (r)

@[elab_without_expected_type] lemma irrefl_of [IsIrrefl α r] (a : α) : ¬a ≺ a := irrefl a
@[elab_without_expected_type] lemma refl_of [IsRefl α r] (a : α) : a ≺ a := refl a
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := _root_.trans
@[elab_without_expected_type] lemma symm_of [IsSymm α r] : a ≺ b → b ≺ a := symm
@[elab_without_expected_type] lemma asymm_of [IsAsymm α r] : a ≺ b → ¬b ≺ a := asymm

@[elab_without_expected_type]
lemma total_of [IsTotal α r] (a b : α) : a ≺ b ∨ b ≺ a := IsTotal.total _ _

@[elab_without_expected_type]
lemma trichotomous_of [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

end

/-! ### Bundled classes -/

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
@[trans] lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

lemma lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_le _ _

lemma lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_le.2 ⟨hab, hba⟩

@[deprecated (since := "2024-07-30")]
theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | _a, _b, hab => lt_iff_le_not_le.mp hab

lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_le.1 hab).1
lemma not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_le.1 hab).2
lemma not_le_of_gt (hab : a > b) : ¬a ≤ b := not_le_of_lt hab
lemma not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
lemma not_lt_of_ge (hab : a ≥ b) : ¬a < b := not_lt_of_le hab

alias LT.lt.not_le := not_le_of_lt
alias LE.le.not_lt := not_lt_of_le

@[trans] lemma ge_trans : a ≥ b → b ≥ c → a ≥ c := fun h₁ h₂ => le_trans h₂ h₁

lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_lt h le_rfl
lemma gt_irrefl (a : α) : ¬a > a := lt_irrefl _

@[trans] lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

@[trans] lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_le (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_lt hbc (le_trans hca hab)

@[trans] lemma gt_of_gt_of_ge (h₁ : a > b) (h₂ : b ≥ c) : a > c := lt_of_le_of_lt h₂ h₁
@[trans] lemma gt_of_ge_of_gt (h₁ : a ≥ b) (h₂ : b > c) : a > c := lt_of_lt_of_le h₂ h₁

@[trans] lemma lt_trans (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)
@[trans] lemma gt_trans : a > b → b > c → a > c := fun h₁ h₂ => lt_trans h₂ h₁

lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
lemma ne_of_gt (h : b < a) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

alias not_lt_of_gt := lt_asymm
alias not_lt_of_lt := lt_asymm

lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a ≤ b := h.elim le_of_eq le_of_lt

instance (priority := 900) : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance (priority := 900) : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance (priority := 900) : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GE.ge GT.gt := ⟨gt_of_gt_of_ge⟩
instance (priority := 900) : @Trans α α α GE.ge GT.gt GT.gt := ⟨gt_of_ge_of_gt⟩

/-- `<` is decidable if `≤` is. -/
def decidableLTOfDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isFalse fun hab' => not_le_of_gt hab' hba
      else isTrue <| lt_of_le_not_le hab hba
    else isFalse fun hab' => hab (le_of_lt hab')

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

variable [PartialOrder α] {a b : α}

lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

alias eq_of_le_of_le := le_antisymm

lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_le h₁ <| mt (le_antisymm h₁) h₂

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [@DecidableRel α (· ≤ ·)] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

namespace Decidable

variable [@DecidableRel α (· ≤ ·)]

lemma lt_or_eq_of_le (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_le hab hba)

lemma eq_or_lt_of_le (hab : a ≤ b) : a = b ∨ a < b :=
  (lt_or_eq_of_le hab).symm

lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

end Decidable

attribute [local instance] Classical.propDecidable

lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := Decidable.lt_or_eq_of_le
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := Decidable.le_iff_lt_or_eq

end PartialOrder

section LinearOrder

/-!
### Definition of `LinearOrder` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def maxDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then b else a

/-- Default definition of `min`. -/
def minDefault {α : Type u} [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] (a b : α) :=
  if a ≤ b then a else b

/-- This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
`compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
  (useful when `compare` is defined via a `match` statement, as it is for `Bool`) -/
macro "compareOfLessAndEq_rfl" : tactic =>
  `(tactic| (intros a b; first | rfl |
    (simp only [compare, compareOfLessAndEq]; split_ifs <;> rfl) |
    (induction a <;> induction b <;> simp (config := {decide := true}) only [])))

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type u) extends PartialOrder α, Min α, Max α, Ord α :=
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop) :=
    @decidableLTOfDecidableLE _ _ decidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

variable [LinearOrder α] {a b c : α}

attribute [local instance] LinearOrder.decidableLE

lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := LinearOrder.le_total

lemma le_of_not_ge : ¬a ≥ b → a ≤ b := (le_total b a).resolve_left
lemma le_of_not_le : ¬a ≤ b → b ≤ a := (le_total a b).resolve_left
lemma lt_of_not_ge (h : ¬a ≥ b) : a < b := lt_of_le_not_le (le_of_not_ge h) h

lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  Or.elim (le_total a b)
    (fun h : a ≤ b =>
      Or.elim (Decidable.lt_or_eq_of_le h) (fun h : a < b => Or.inl h) fun h : a = b =>
        Or.inr (Or.inl h))
    fun h : b ≤ a =>
    Or.elim (Decidable.lt_or_eq_of_le h) (fun h : b < a => Or.inr (Or.inr h)) fun h : b = a =>
      Or.inr (Or.inl h.symm)

lemma le_of_not_lt (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h

lemma le_of_not_gt : ¬a > b → a ≤ b := le_of_not_lt

lemma lt_or_le (a b : α) : a < b ∨ b ≤ a :=
  if hba : b ≤ a then Or.inr hba else Or.inl <| lt_of_not_ge hba

lemma le_or_lt (a b : α) : a ≤ b ∨ b < a := (lt_or_le b a).symm
lemma lt_or_ge : ∀ a b : α, a < b ∨ a ≥ b := lt_or_le
lemma le_or_gt : ∀ a b : α, a ≤ b ∨ a > b := le_or_lt

lemma lt_or_gt_of_ne (h : a ≠ b) : a < b ∨ a > b := by simpa [h] using lt_trichotomy a b

lemma ne_iff_lt_or_gt : a ≠ b ↔ a < b ∨ a > b := ⟨lt_or_gt_of_ne, (Or.elim · ne_of_lt ne_of_gt)⟩

lemma lt_iff_not_ge (x y : α) : x < y ↔ ¬x ≥ y := ⟨not_le_of_gt, lt_of_not_ge⟩

@[simp] lemma not_lt : ¬a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩
@[simp] lemma not_le : ¬a ≤ b ↔ b < a := (lt_iff_not_ge _ _).symm

instance (priority := 900) (a b : α) : Decidable (a < b) := LinearOrder.decidableLT a b
instance (priority := 900) (a b : α) : Decidable (a ≤ b) := LinearOrder.decidableLE a b
instance (priority := 900) (a b : α) : Decidable (a = b) := LinearOrder.decidableEq a b

lemma eq_or_lt_of_not_lt (h : ¬a < b) : a = b ∨ b < a :=
  if h₁ : a = b then Or.inl h₁ else Or.inr (lt_of_not_ge fun hge => h (lt_of_le_of_ne hge h₁))

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictTotalOrder_of_linearOrder : IsStrictTotalOrder α (· < ·) where
  irrefl := lt_irrefl
  trichotomous := lt_trichotomy

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def ltByCases (x y : α) {P : Sort*} (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
  if h : x < y then h₁ h
  else if h' : y < x then h₃ h' else h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

namespace Nat

/-! Deprecated properties of inequality on `Nat` -/

@[deprecated (since := "2024-08-23")]
protected def ltGeByCases {a b : Nat} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
  Decidable.byCases h₁ fun h => h₂ (Or.elim (Nat.lt_or_ge a b) (fun a => absurd a h) fun a => a)

set_option linter.deprecated false in
@[deprecated ltByCases (since := "2024-08-23")]
protected def ltByCases {a b : Nat} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
    (h₃ : b < a → C) : C :=
  Nat.ltGeByCases h₁ fun h₁ => Nat.ltGeByCases h₃ fun h => h₂ (Nat.le_antisymm h h₁)

end Nat

theorem le_imp_le_of_lt_imp_lt {α β} [Preorder α] [LinearOrder β] {a b : α} {c d : β}
    (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_lt fun h' => not_le_of_gt (H h') h

lemma min_def (a b : α) : min a b = if a ≤ b then a else b := by rw [LinearOrder.min_def a]
lemma max_def (a b : α) : max a b = if a ≤ b then b else a := by rw [LinearOrder.max_def a]

-- Porting note: no `min_tac` tactic in the following series of lemmas

lemma min_le_left (a b : α) : min a b ≤ a := by
  if h : a ≤ b
  then simp [min_def, if_pos h, le_refl]
  else simp [min_def, if_neg h]; exact le_of_not_le h

lemma min_le_right (a b : α) : min a b ≤ b := by
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h
  else simp [min_def, if_neg h, le_refl]

lemma le_min (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := by
  if h : a ≤ b
  then simp [min_def, if_pos h]; exact h₁
  else simp [min_def, if_neg h]; exact h₂

lemma le_max_left (a b : α) : a ≤ max a b := by
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h
  else simp [max_def, if_neg h, le_refl]

lemma le_max_right (a b : α) : b ≤ max a b := by
  if h : a ≤ b
  then simp [max_def, if_pos h, le_refl]
  else simp [max_def, if_neg h]; exact le_of_not_le h

lemma max_le (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := by
  if h : a ≤ b
  then simp [max_def, if_pos h]; exact h₂
  else simp [max_def, if_neg h]; exact h₁

lemma eq_min (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀ {d}, d ≤ a → d ≤ b → d ≤ c) : c = min a b :=
  le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

lemma min_comm (a b : α) : min a b = min b a :=
  eq_min (min_le_right a b) (min_le_left a b) fun h₁ h₂ => le_min h₂ h₁

lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) := by
  apply eq_min
  · apply le_trans; apply min_le_left; apply min_le_left
  · apply le_min; apply le_trans; apply min_le_left; apply min_le_right; apply min_le_right
  · intro d h₁ h₂; apply le_min; apply le_min h₁; apply le_trans h₂; apply min_le_left
    apply le_trans h₂; apply min_le_right

lemma min_left_comm : ∀ a b c : α, min a (min b c) = min b (min a c) :=
  left_comm (@min α _) (@min_comm α _) (@min_assoc α _)

@[simp] lemma min_self (a : α) : min a a = a := by simp [min_def]

lemma min_eq_left (h : a ≤ b) : min a b = a := by
  apply Eq.symm; apply eq_min (le_refl _) h; intros; assumption

lemma min_eq_right (h : b ≤ a) : min a b = b := min_comm b a ▸ min_eq_left h

lemma eq_max (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀ {d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

lemma max_comm (a b : α) : max a b = max b a :=
  eq_max (le_max_right a b) (le_max_left a b) fun h₁ h₂ => max_le h₂ h₁

lemma max_assoc (a b c : α) : max (max a b) c = max a (max b c) := by
  apply eq_max
  · apply le_trans; apply le_max_left a b; apply le_max_left
  · apply max_le; apply le_trans; apply le_max_right a b; apply le_max_left; apply le_max_right
  · intro d h₁ h₂; apply max_le; apply max_le h₁; apply le_trans (le_max_left _ _) h₂
    apply le_trans (le_max_right _ _) h₂

lemma max_left_comm : ∀ a b c : α, max a (max b c) = max b (max a c) :=
  left_comm (@max α _) (@max_comm α _) (@max_assoc α _)

@[simp] lemma max_self (a : α) : max a a = a := by simp [max_def]

lemma max_eq_left (h : b ≤ a) : max a b = a := by
  apply Eq.symm; apply eq_max (le_refl _) h; intros; assumption

lemma max_eq_right (h : a ≤ b) : max a b = b := max_comm b a ▸ max_eq_left h

lemma min_eq_left_of_lt (h : a < b) : min a b = a := min_eq_left (le_of_lt h)
lemma min_eq_right_of_lt (h : b < a) : min a b = b := min_eq_right (le_of_lt h)
lemma max_eq_left_of_lt (h : b < a) : max a b = a := max_eq_left (le_of_lt h)
lemma max_eq_right_of_lt (h : a < b) : max a b = b := max_eq_right (le_of_lt h)

lemma lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c := by
  cases le_total b c <;> simp [min_eq_left, min_eq_right, *]

lemma max_lt (h₁ : a < c) (h₂ : b < c) : max a b < c := by
  cases le_total a b <;> simp [max_eq_left, max_eq_right, *]

section Ord
variable {o : Ordering}

lemma compare_lt_iff_lt : compare a b = .lt ↔ a < b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl]

lemma compare_gt_iff_gt : compare a b = .gt ↔ a > b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> simp only [*, lt_irrefl, not_lt_of_gt]
  case _ h₁ h₂ =>
    have h : b < a := lt_trichotomy a b |>.resolve_left h₁ |>.resolve_left h₂
    exact true_iff_iff.2 h

lemma compare_eq_iff_eq : compare a b = .eq ↔ a = b := by
  rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
  split_ifs <;> try simp only
  case _ h   => exact false_iff_iff.2 <| ne_iff_lt_or_gt.2 <| .inl h
  case _ _ h => exact true_iff_iff.2 h
  case _ _ h => exact false_iff_iff.2 h

lemma compare_le_iff_le : compare a b ≠ .gt ↔ a ≤ b := by
  cases h : compare a b <;> simp
  · exact le_of_lt <| compare_lt_iff_lt.1 h
  · exact le_of_eq <| compare_eq_iff_eq.1 h
  · exact compare_gt_iff_gt.1 h

lemma compare_ge_iff_ge : compare a b ≠ .lt ↔ a ≥ b := by
  cases h : compare a b <;> simp
  · exact compare_lt_iff_lt.1 h
  · exact le_of_eq <| (·.symm) <| compare_eq_iff_eq.1 h
  · exact le_of_lt <| compare_gt_iff_gt.1 h

lemma compare_iff (a b : α) : compare a b = o ↔ o.toRel a b := by
  cases o <;> simp only [Ordering.toRel]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

instance : Batteries.TransCmp (compare (α := α)) where
  symm a b := by
    cases h : compare a b <;>
    simp only [Ordering.swap] <;> symm
    · exact compare_gt_iff_gt.2 <| compare_lt_iff_lt.1 h
    · exact compare_eq_iff_eq.2 <| compare_eq_iff_eq.1 h |>.symm
    · exact compare_lt_iff_lt.2 <| compare_gt_iff_gt.1 h
  le_trans := fun h₁ h₂ ↦
    compare_le_iff_le.2 <| le_trans (compare_le_iff_le.1 h₁) (compare_le_iff_le.1 h₂)

end Ord

end LinearOrder
