/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Defs
import Batteries.Tactic.Alias
import Mathlib.Tactic.ExtendDoc


/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

@[expose] public section

/-! ### Unbundled classes -/

/-- An empty relation does not relate any elements. -/
@[deprecated (since := "2025-12-22")] alias EmptyRelation := emptyRelation

/-- `IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
@[deprecated Std.Irrefl (since := "2026-01-07")]
abbrev IsIrrefl (α : Sort*) (r : α → α → Prop) : Prop := Std.Irrefl r

/-- `IsRefl X r` means the binary relation `r` on `X` is reflexive. -/
@[deprecated Std.Refl (since := "2026-01-08")]
abbrev IsRefl (α : Sort*) (r : α → α → Prop) : Prop := Std.Refl r

/-- `IsSymm X r` means the binary relation `r` on `X` is symmetric. -/
@[deprecated Std.Symm (since := "2025-12-26")]
abbrev IsSymm (α : Sort*) (r : α → α → Prop) : Prop := Std.Symm r

/-- `IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
@[deprecated Std.Asymm (since := "2026-01-03")]
abbrev IsAsymm (α : Sort*) (r : α → α → Prop) : Prop := Std.Asymm r

/-- `IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
@[deprecated Std.Antisymm (since := "2026-01-06")]
abbrev IsAntisymm (α : Sort*) (r : α → α → Prop) : Prop := Std.Antisymm r

/-- `IsTrans X r` means the binary relation `r` on `X` is transitive. -/
class IsTrans (α : Sort*) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c

instance {α : Sort*} {r : α → α → Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩

instance (priority := 100) {α : Sort*} {r : α → α → Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩

/-- `IsTotal X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
@[deprecated Std.Total (since := "2026-01-09")]
abbrev IsTotal (α : Sort*) (r : α → α → Prop) : Prop := Std.Total r

/-- `IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop extends Std.Refl r, IsTrans α r

/-- `IsPartialOrder X r` means that the binary relation `r` on `X` is a partial order, that is,
`IsPreorder X r` and `Std.Antisymm r`. -/
class IsPartialOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, Std.Antisymm r

/-- `IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order, that is,
`IsPartialOrder X r` and `Std.Total r`. -/
class IsLinearOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPartialOrder α r, Std.Total r

/-- `IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `IsPreorder X r` and `Std.Symm r`. -/
class IsEquiv (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, Std.Symm r

/-- `IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order, that is,
`Std.Irrefl r` and `IsTrans X r`. -/
class IsStrictOrder (α : Sort*) (r : α → α → Prop) : Prop extends Std.Irrefl r, IsTrans α r

/-- `IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `IsStrictOrder X lt` and `¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a`. -/
class IsStrictWeakOrder (α : Sort*) (lt : α → α → Prop) : Prop extends IsStrictOrder α lt where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
@[deprecated Std.Trichotomous (since := "2026-01-24")]
abbrev IsTrichotomous (α : Sort*) (lt : α → α → Prop) : Prop := Std.Trichotomous lt

/-- `IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `Std.Trichotomous lt` and `IsStrictOrder X lt`. -/
class IsStrictTotalOrder (α : Sort*) (lt : α → α → Prop) : Prop
    extends Std.Trichotomous lt, IsStrictOrder α lt

theorem Equivalence.of_isEquiv {α : Sort*} (lt : α → α → Prop) [IsEquiv α lt] : Equivalence lt where
  refl := Std.Refl.refl; symm := Std.Symm.symm _ _; trans := IsTrans.trans _ _ _

theorem IsEquiv.of_equivalence {α : Sort*} {lt : α → α → Prop} (h : Equivalence lt) :
    IsEquiv α lt where
  refl := h.refl; symm _ _ := h.symm; trans _ _ _ := h.trans

theorem equivalence_iff_isEquiv {α : Sort*} (lt : α → α → Prop) : Equivalence lt ↔ IsEquiv α lt :=
  ⟨.of_equivalence, fun _ => .of_isEquiv lt⟩

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

lemma irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a := Std.Irrefl.irrefl a
lemma refl [Std.Refl r] (a : α) : a ≺ a := Std.Refl.refl a
lemma trans [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
lemma symm [Std.Symm r] : a ≺ b → b ≺ a := Std.Symm.symm _ _
lemma antisymm [Std.Antisymm r] : a ≺ b → b ≺ a → a = b := Std.Antisymm.antisymm _ _
lemma asymm [Std.Asymm r] : a ≺ b → ¬b ≺ a := Std.Asymm.asymm _ _

lemma trichotomous [Std.Trichotomous r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  fun _ _ ↦ Std.Trichotomous.rel_or_eq_or_rel_swap

lemma irrefl_def : Std.Irrefl r ↔ ∀ ⦃a⦄, ¬r a a :=
  ⟨(·.irrefl), .mk⟩

lemma refl_def : Std.Refl r ↔ ∀ ⦃a⦄, r a a :=
  ⟨(·.refl), .mk⟩

lemma isTrans_def {α : Sort*} {r : α → α → Prop} : IsTrans α r ↔ ∀ ⦃a b c⦄, r a b → r b c → r a c :=
  ⟨(·.trans), .mk⟩

lemma symm_def : Std.Symm r ↔ ∀ ⦃a b⦄, r a b → r b a :=
  ⟨(·.symm), .mk⟩

lemma antisymm_def : Std.Antisymm r ↔ ∀ ⦃a b⦄, r a b → r b a → a = b :=
  ⟨(·.antisymm), .mk⟩

lemma asymm_def : Std.Asymm r ↔ ∀ ⦃a b⦄, r a b → ¬r b a :=
  ⟨(·.asymm), .mk⟩

lemma total_def : Std.Total r ↔ ∀ ⦃a b⦄, r a b ∨ r b a :=
  ⟨(·.total), .mk⟩

lemma trichotomous_def : Std.Trichotomous r ↔ ∀ ⦃a b⦄, ¬r a b → ¬r b a → a = b :=
  ⟨(·.trichotomous), .mk⟩

instance (priority := 90) asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩

instance Std.Irrefl.decide [DecidableRel r] [Std.Irrefl r] :
    Std.Irrefl (fun a b => decide (r a b) = true) where
  irrefl := fun a => by simpa using irrefl a

instance Std.Refl.decide [DecidableRel r] [Std.Refl r] :
    Std.Refl (fun a b => decide (r a b) = true) where
  refl := fun a => by simpa using refl a

instance IsTrans.decide [DecidableRel r] [IsTrans α r] :
    IsTrans α (fun a b => decide (r a b) = true) where
  trans := fun a b c => by simpa using trans a b c

instance Std.Symm.decide [DecidableRel r] [Std.Symm r] :
    Std.Symm (fun a b => decide (r a b) = true) where
  symm := fun a b => by simpa using symm a b

instance Std.Antisymm.decide [DecidableRel r] [Std.Antisymm r] :
    Std.Antisymm (fun a b => decide (r a b) = true) where
  antisymm a b h₁ h₂ := antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)

instance Std.Asymm.decide [DecidableRel r] [Std.Asymm r] :
    Std.Asymm (fun a b => decide (r a b) = true) where
  asymm := fun a b => by simpa using asymm a b

instance Std.Total.decide [DecidableRel r] [Std.Total r] :
    Std.Total (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b

instance Std.Trichotomous.decide [DecidableRel r] [Std.Trichotomous r] :
    Std.Trichotomous (fun a b => decide (r a b) = true) where
  trichotomous a b := by simpa using trichotomous a b

variable (r)

@[elab_without_expected_type] lemma irrefl_of [Std.Irrefl r] (a : α) : ¬a ≺ a := irrefl a
@[elab_without_expected_type] lemma refl_of [Std.Refl r] (a : α) : a ≺ a := refl a
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := _root_.trans
@[elab_without_expected_type] lemma symm_of [Std.Symm r] : a ≺ b → b ≺ a := symm
@[elab_without_expected_type] lemma asymm_of [Std.Asymm r] : a ≺ b → ¬b ≺ a := asymm

@[elab_without_expected_type]
lemma total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a := Std.Total.total _ _

@[elab_without_expected_type]
lemma trichotomous_of [Std.Trichotomous r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

section

/-- `Std.Refl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Refl (since := "2026-03-27")]
def Reflexive := ∀ x, x ≺ x

/-- `Std.Symm` as a definition, suitable for use in proofs. -/
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- `IsTrans` as a definition, suitable for use in proofs. -/
@[deprecated IsTrans (since := "2026-02-20")]
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

/-- `Std.Irrefl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Irrefl (since := "2026-02-12")]
def Irreflexive := ∀ x, ¬x ≺ x

/-- `Std.Antisymm` as a definition, suitable for use in proofs. -/
@[deprecated Std.Antisymm (since := "2026-02-09")]
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- `Std.Total` as a definition, suitable for use in proofs. -/
@[deprecated Std.Total (since := "2026-02-10")]
def Total := ∀ x y, x ≺ y ∨ y ≺ x

theorem Equivalence.stdRefl (h : Equivalence r) : Std.Refl r where
  refl := h.refl

@[deprecated (since := "2026-03-27")] alias Equivalence.reflexive := Equivalence.stdRefl

theorem Equivalence.symmetric (h : Equivalence r) : Symmetric r :=
  fun _ _ ↦ h.symm

theorem Equivalence.isTrans (h : Equivalence r) : IsTrans α r :=
  ⟨fun _ _ _ ↦ h.trans⟩

@[deprecated (since := "2026-02-20")] alias Equivalence.transitive := Equivalence.isTrans

variable {β : Sort*} (r : β → β → Prop) (f : α → β)

instance InvImage.isTrans [IsTrans β r] : IsTrans α (InvImage r f) :=
  ⟨fun _ _ _ ↦ trans_of r⟩

@[deprecated (since := "2026-02-20")] alias InvImage.trans := InvImage.isTrans

instance InvImage.irrefl [Std.Irrefl r] : Std.Irrefl (InvImage r f) :=
  ⟨fun (a : α) (h₁ : InvImage r f a a) ↦ irrefl_of r (f a) h₁⟩

@[deprecated (since := "2026-02-12")] alias InvImage.irreflexive := InvImage.irrefl

end

end

/-! ### Minimal and maximal -/

section LE

variable {α : Type*} [LE α] {P : α → Prop} {x y : α}

/-- `Minimal P x` means that `x` is a minimal element satisfying `P`. -/
@[to_dual /-- `Maximal P x` means that `x` is a maximal element satisfying `P`. -/]
def Minimal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y

@[to_dual]
lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1

@[to_dual le_of_ge] -- TODO: improve this naming
lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y ≤ x) : x ≤ y :=
  h.2 hy hle

end LE

section LE
variable {ι : Sort*} {α : Type*} [LE α] {P : ι → Prop} {f : ι → α} {i j : ι}

/-- `MinimalFor P f i` means that `f i` is minimal over all `i` satisfying `P`. -/
@[to_dual /-- `MaximalFor P f i` means that `f i` is maximal over all `i` satisfying `P`. -/]
def MinimalFor (P : ι → Prop) (f : ι → α) (i : ι) : Prop := P i ∧ ∀ ⦃j⦄, P j → f j ≤ f i → f i ≤ f j

@[to_dual]
lemma MinimalFor.prop (h : MinimalFor P f i) : P i := h.1

@[to_dual]
lemma MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P j) (hji : f j ≤ f i) : f i ≤ f j :=
  h.2 hj hji

end LE

/-! ### Upper and lower sets -/

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
@[to_dual /-- A lower set in an order `α` is a set such that any element less than one of its
members is also a member. Also called down-set, downward-closed set. -/]
def IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

@[inherit_doc IsUpperSet]
structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet, to_dual]
structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."

/-- An upper set relative to a predicate `P` is a set such that all elements satisfy `P` and
any element greater than one of its members and satisfying `P` is also a member. -/
@[to_dual /-- A lower set relative to a predicate `P` is a set such that all elements satisfy `P`
and any element less than one of its members and satisfying `P` is also a member. -/]
def IsRelUpperSet {α : Type*} [LE α] (s : Set α) (P : α → Prop) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → P a ∧ ∀ ⦃b : α⦄, a ≤ b → P b → b ∈ s

@[inherit_doc IsRelUpperSet]
structure RelUpperSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelUpperSet`. -/
  carrier : Set α
  /-- The carrier of a `RelUpperSet` is an upper set relative to `P`.

  Do NOT use directly. Please use `RelUpperSet.isRelUpperSet` instead. -/
  isRelUpperSet' : IsRelUpperSet carrier P

extend_docs RelUpperSet before "The type of upper sets of an order relative to `P`."

@[inherit_doc IsRelLowerSet, to_dual]
structure RelLowerSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelLowerSet`. -/
  carrier : Set α
  /-- The carrier of a `RelLowerSet` is a lower set relative to `P`.

  Do NOT use directly. Please use `RelLowerSet.isRelLowerSet` instead. -/
  isRelLowerSet' : IsRelLowerSet carrier P

extend_docs RelLowerSet before "The type of lower sets of an order relative to `P`."

variable {α β : Sort*} {r : α → α → Prop} {s : β → β → Prop}

theorem of_eq [Std.Refl r] : ∀ {a b}, a = b → r a b
  | _, _, .refl _ => refl _

theorem comm [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩

theorem antisymm' [Std.Antisymm r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h

theorem antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
theorem antisymm_of (r : α → α → Prop) [Std.Antisymm r] {a b : α} : r a b → r b a → a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
theorem antisymm_of' (r : α → α → Prop) [Std.Antisymm r] {a b : α} : r a b → r b a → b = a :=
  antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
theorem comm_of (r : α → α → Prop) [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  comm

protected theorem Std.Asymm.antisymm (r : α → α → Prop) [Std.Asymm r] : Std.Antisymm r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isAntisymm := Std.Asymm.antisymm
@[deprecated (since := "2026-01-06")] protected alias Std.Asymm.isAntisymm := Std.Asymm.antisymm

protected theorem Std.Asymm.irrefl [Std.Asymm r] : Std.Irrefl r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isIrrefl := Std.Asymm.irrefl
@[deprecated (since := "2026-01-07")] protected alias Std.Asymm.isIrrefl := Std.Asymm.irrefl

protected theorem Std.Total.trichotomous (r : α → α → Prop) [Std.Total r] : Std.Trichotomous r :=
  inferInstance

@[deprecated (since := "2026-01-24")] alias Std.Total.isTrichotomous := Std.Total.trichotomous

-- see Note [lower instance priority]
instance (priority := 100) Std.Total.to_refl (r : α → α → Prop) [Std.Total r] : Std.Refl r :=
  inferInstance

theorem ne_of_irrefl {r} [Std.Irrefl r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h

theorem ne_of_irrefl' {r} [Std.Irrefl r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h

theorem not_rel_of_subsingleton (r : α → α → Prop) [Std.Irrefl r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x

theorem rel_of_subsingleton (r : α → α → Prop) [Std.Refl r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x

@[simp]
theorem empty_relation_apply (a b : α) : emptyRelation a b ↔ False :=
  Iff.rfl

instance : @Std.Irrefl α emptyRelation :=
  ⟨fun _ => id⟩

theorem rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b) : r a c ↔ r b c :=
  ⟨trans_of r (symm_of r h), trans_of r h⟩

theorem rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c) : r a b ↔ r a c :=
  ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩

theorem rel_congr [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d) :
    r a c ↔ r b d := by
  rw [rel_congr_left h₁, rel_congr_right h₂]

theorem trans_trichotomous_left [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : ¬r b a) (h₂ : r b c) : r a c := by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁

theorem trans_trichotomous_right [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : r a b) (h₂ : ¬r c b) : r a c := by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

set_option linter.deprecated false in
@[deprecated IsTrans.trans (since := "2026-02-20")]
theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := IsTrans.trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [Std.Trichotomous r] [Std.Irrefl r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right <| mt (H _).1
    <| irrefl b
