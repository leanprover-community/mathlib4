/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

-- TODO: documentation uses X for α

/-! ### Unbundled classes -/

/-- An empty relation does not relate any elements. -/
@[nolint unusedArguments] def EmptyRelation {α : Sort*} := fun _ _ : α ↦ False

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
@[deprecated Std.Total (since := "2025-10-23")]
class IsTotal (α : Sort*) (r : α → α → Prop) : Prop where
  total : ∀ a b, r a b ∨ r b a

set_option linter.deprecated false in
@[deprecated Std.Total (since := "2025-10-23")]
instance {α : Sort*} (r) [Std.Total r] : IsTotal α r where
  total := Std.Total.total

/-- `IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop extends IsRefl α r, IsTrans α r

/-- `IsPartialOrder X r` means that the binary relation `r` on `X` is a partial order, that is,
`IsPreorder X r` and `IsAntisymm X r`. -/
class IsPartialOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, IsAntisymm α r

/-- `IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order, that is,
`IsPartialOrder X r` and `Std.Total r`. -/
class IsLinearOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPartialOrder α r, Std.Total r

/-- `IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `IsPreorder X r` and `IsSymm X r`. -/
class IsEquiv (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, IsSymm α r

/-- `IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order, that is,
`IsIrrefl X r` and `IsTrans X r`. -/
class IsStrictOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsIrrefl α r, IsTrans α r

/-- `IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `IsStrictOrder X lt` and `¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a`. -/
class IsStrictWeakOrder (α : Sort*) (lt : α → α → Prop) : Prop extends IsStrictOrder α lt where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
class IsTrichotomous (α : Sort*) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a

/-- `IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `IsTrichotomous X lt` and `IsStrictOrder X lt`. -/
class IsStrictTotalOrder (α : Sort*) (lt : α → α → Prop) : Prop
    extends IsTrichotomous α lt, IsStrictOrder α lt

/-- Equality is an equivalence relation. -/
instance eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

/-- `Iff` is an equivalence relation. -/
instance iff_isEquiv : IsEquiv Prop Iff where
  symm := @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl

section

variable {α : Sort*} {r : α → α → Prop} {a b c : α}

/-- Local notation for an arbitrary binary relation `r`. -/
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

instance IsIrrefl.decide [DecidableRel r] [IsIrrefl α r] :
    IsIrrefl α (fun a b => decide (r a b) = true) where
  irrefl := fun a => by simpa using irrefl a

instance IsRefl.decide [DecidableRel r] [IsRefl α r] :
    IsRefl α (fun a b => decide (r a b) = true) where
  refl := fun a => by simpa using refl a

instance IsTrans.decide [DecidableRel r] [IsTrans α r] :
    IsTrans α (fun a b => decide (r a b) = true) where
  trans := fun a b c => by simpa using trans a b c

instance IsSymm.decide [DecidableRel r] [IsSymm α r] :
    IsSymm α (fun a b => decide (r a b) = true) where
  symm := fun a b => by simpa using symm a b

instance IsAntisymm.decide [DecidableRel r] [IsAntisymm α r] :
    IsAntisymm α (fun a b => decide (r a b) = true) where
  antisymm a b h₁ h₂ := antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)

instance IsAsymm.decide [DecidableRel r] [IsAsymm α r] :
    IsAsymm α (fun a b => decide (r a b) = true) where
  asymm := fun a b => by simpa using asymm a b

instance Std.Total.decide [DecidableRel r] [Std.Total r] :
    Std.Total (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b

set_option linter.deprecated false in
@[deprecated Std.Total.decide (since := "2025-10-23")]
instance IsTotal.decide [DecidableRel r] [IsTotal α r] :
    IsTotal α (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b

instance IsTrichotomous.decide [DecidableRel r] [IsTrichotomous α r] :
    IsTrichotomous α (fun a b => decide (r a b) = true) where
  trichotomous := fun a b => by simpa using trichotomous a b

variable (r)

@[elab_without_expected_type] lemma irrefl_of [IsIrrefl α r] (a : α) : ¬a ≺ a := irrefl a
@[elab_without_expected_type] lemma refl_of [IsRefl α r] (a : α) : a ≺ a := refl a
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := _root_.trans
@[elab_without_expected_type] lemma symm_of [IsSymm α r] : a ≺ b → b ≺ a := symm
@[elab_without_expected_type] lemma asymm_of [IsAsymm α r] : a ≺ b → ¬b ≺ a := asymm

set_option linter.deprecated false in
@[elab_without_expected_type, deprecated Std.Total.total (since := "2025-10-23")]
lemma total_of [IsTotal α r] (a b : α) : a ≺ b ∨ b ≺ a := IsTotal.total _ _

@[elab_without_expected_type]
lemma trichotomous_of [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

section

/-- `IsRefl` as a definition, suitable for use in proofs. -/
def Reflexive := ∀ x, x ≺ x

/-- `IsSymm` as a definition, suitable for use in proofs. -/
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- `IsTrans` as a definition, suitable for use in proofs. -/
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

/-- `IsIrrefl` as a definition, suitable for use in proofs. -/
def Irreflexive := ∀ x, ¬x ≺ x

/-- `IsAntisymm` as a definition, suitable for use in proofs. -/
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- `IsTotal` as a definition, suitable for use in proofs. -/
def Total := ∀ x y, x ≺ y ∨ y ≺ x

theorem Equivalence.reflexive (h : Equivalence r) : Reflexive r := h.refl

theorem Equivalence.symmetric (h : Equivalence r) : Symmetric r :=
  fun _ _ ↦ h.symm

theorem Equivalence.transitive (h : Equivalence r) : Transitive r :=
  fun _ _ _ ↦ h.trans

variable {β : Sort*} (r : β → β → Prop) (f : α → β)

theorem InvImage.trans (h : Transitive r) : Transitive (InvImage r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : InvImage r f a₁ a₂) (h₂ : InvImage r f a₂ a₃) ↦ h h₁ h₂

theorem InvImage.irreflexive (h : Irreflexive r) : Irreflexive (InvImage r f) :=
  fun (a : α) (h₁ : InvImage r f a a) ↦ h (f a) h₁

end

end

/-! ### Minimal and maximal -/

section LE

variable {α : Type*} [LE α] {P : α → Prop} {x y : α}

/-- `Minimal P x` means that `x` is a minimal element satisfying `P`. -/
def Minimal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y

/-- `Maximal P x` means that `x` is a maximal element satisfying `P`. -/
def Maximal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → x ≤ y → y ≤ x

lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1

lemma Maximal.prop (h : Maximal P x) : P x :=
  h.1

lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y ≤ x) : x ≤ y :=
  h.2 hy hle

lemma Maximal.le_of_ge (h : Maximal P x) (hy : P y) (hge : x ≤ y) : y ≤ x :=
  h.2 hy hge

end LE

section LE
variable {ι : Sort*} {α : Type*} [LE α] {P : ι → Prop} {f : ι → α} {i j : ι}

/-- `MinimalFor P f i` means that `f i` is minimal over all `i` satisfying `P`. -/
def MinimalFor (P : ι → Prop) (f : ι → α) (i : ι) : Prop := P i ∧ ∀ ⦃j⦄, P j → f j ≤ f i → f i ≤ f j

/-- `MaximalFor P f i` means that `f i` is maximal over all `i` satisfying `P`. -/
def MaximalFor (P : ι → Prop) (f : ι → α) (i : ι) : Prop := P i ∧ ∀ ⦃j⦄, P j → f i ≤ f j → f j ≤ f i

lemma MinimalFor.prop (h : MinimalFor P f i) : P i := h.1
lemma MaximalFor.prop (h : MaximalFor P f i) : P i := h.1

lemma MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P j) (hji : f j ≤ f i) : f i ≤ f j :=
  h.2 hj hji

lemma MaximalFor.le_of_le (h : MaximalFor P f i) (hj : P j) (hij : f i ≤ f j) : f j ≤ f i :=
  h.2 hj hij

end LE

/-! ### Upper and lower sets -/

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

@[inherit_doc IsUpperSet]
structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet]
structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."

/-- An upper set relative to a predicate `P` is a set such that all elements satisfy `P` and
any element greater than one of its members and satisfying `P` is also a member. -/
def IsRelUpperSet {α : Type*} [LE α] (s : Set α) (P : α → Prop) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → P a ∧ ∀ ⦃b : α⦄, a ≤ b → P b → b ∈ s

/-- A lower set relative to a predicate `P` is a set such that all elements satisfy `P` and
any element less than one of its members and satisfying `P` is also a member. -/
def IsRelLowerSet {α : Type*} [LE α] (s : Set α) (P : α → Prop) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → P a ∧ ∀ ⦃b : α⦄, b ≤ a → P b → b ∈ s

@[inherit_doc IsRelUpperSet]
structure RelUpperSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelUpperSet`. -/
  carrier : Set α
  /-- The carrier of a `RelUpperSet` is an upper set relative to `P`.

  Do NOT use directly. Please use `RelUpperSet.isRelUpperSet` instead. -/
  isRelUpperSet' : IsRelUpperSet carrier P

extend_docs RelUpperSet before "The type of upper sets of an order relative to `P`."

@[inherit_doc IsRelLowerSet]
structure RelLowerSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelLowerSet`. -/
  carrier : Set α
  /-- The carrier of a `RelLowerSet` is a lower set relative to `P`.

  Do NOT use directly. Please use `RelLowerSet.isRelLowerSet` instead. -/
  isRelLowerSet' : IsRelLowerSet carrier P

extend_docs RelLowerSet before "The type of lower sets of an order relative to `P`."

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

theorem of_eq [IsRefl α r] : ∀ {a b}, a = b → r a b
  | _, _, .refl _ => refl _

theorem comm [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩

theorem antisymm' [IsAntisymm α r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h

theorem antisymm_iff [IsRefl α r] [IsAntisymm α r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
theorem antisymm_of (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
theorem antisymm_of' (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → b = a :=
  antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
theorem comm_of (r : α → α → Prop) [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  comm

protected theorem IsAsymm.isAntisymm (r) [IsAsymm α r] : IsAntisymm α r :=
  ⟨fun _ _ h₁ h₂ => (_root_.asymm h₁ h₂).elim⟩

protected theorem IsAsymm.isIrrefl [IsAsymm α r] : IsIrrefl α r :=
  ⟨fun _ h => _root_.asymm h h⟩

protected theorem Std.Total.isTrichotomous (r) [Std.Total r] : IsTrichotomous α r :=
  ⟨fun a b => or_left_comm.1 (Or.inr <| Std.Total.total a b)⟩

set_option linter.deprecated false in
@[deprecated Std.Total.isTrichotomous (since := "2025-10-23")]
protected theorem IsTotal.isTrichotomous (r) [IsTotal α r] : IsTrichotomous α r :=
  ⟨fun a b => or_left_comm.1 (Or.inr <| total_of r a b)⟩

-- see Note [lower instance priority]
instance (priority := 100) Std.Total.to_isRefl (r) [Std.Total r] : IsRefl α r :=
  ⟨fun a => or_self_iff.1 <| Std.Total.total a a⟩

-- see Note [lower instance priority]
set_option linter.deprecated false in
@[deprecated Std.Total.to_isRefl (since := "2025-10-23")]
instance (priority := 100) IsTotal.to_isRefl (r) [IsTotal α r] : IsRefl α r :=
  ⟨fun a => or_self_iff.1 <| total_of r a a⟩

theorem ne_of_irrefl {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h

theorem ne_of_irrefl' {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h

theorem not_rel_of_subsingleton (r) [IsIrrefl α r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x

theorem rel_of_subsingleton (r) [IsRefl α r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x

@[simp]
theorem empty_relation_apply (a b : α) : EmptyRelation a b ↔ False :=
  Iff.rfl

instance : IsIrrefl α EmptyRelation :=
  ⟨fun _ => id⟩

theorem rel_congr_left [IsSymm α r] [IsTrans α r] {a b c : α} (h : r a b) : r a c ↔ r b c :=
  ⟨trans_of r (symm_of r h), trans_of r h⟩

theorem rel_congr_right [IsSymm α r] [IsTrans α r] {a b c : α} (h : r b c) : r a b ↔ r a c :=
  ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩

theorem rel_congr [IsSymm α r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d) :
    r a c ↔ r b d := by
  rw [rel_congr_left h₁, rel_congr_right h₂]

theorem trans_trichotomous_left [IsTrans α r] [IsTrichotomous α r] {a b c : α}
    (h₁ : ¬r b a) (h₂ : r b c) : r a c := by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁

theorem trans_trichotomous_right [IsTrans α r] [IsTrichotomous α r] {a b c : α}
    (h₁ : r a b) (h₂ : ¬r c b) : r a c := by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := IsTrans.trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [IsTrichotomous α r] [IsIrrefl α r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right <| mt (H _).1
    <| irrefl b

instance Std.Total.inst_ge_of_le [LE α] [Std.Total (α := α) (· ≤ ·)] :
    Std.Total (α := α) (· ≥ ·) where
  total a b := Std.Total.total (r := (· ≤ ·)) b a
