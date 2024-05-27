/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Logic

#align_import init.algebra.classes from "leanprover-community/lean"@"31f3a46d7c18d6b2255a72df4f9d62644145d83b"

/-!
# Unbundled algebra classes

These classes are part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).
However a subset of them are widely used in mathlib3,
and it has been tricky to clean this up as this file was in core Lean 3.

By themselves, these classes are not good replacements for the `Monoid` / `Group` etc structures
provided by mathlib, as they are not discoverable by `simp` unlike the current lemmas due to there
being little to index on. The Wiki page linked above describes an algebraic normalizer, but it was
never implemented in Lean 3.

## Porting note:
This file is ancient, and it would be good to replace it with a clean version
that provides what mathlib4 actually needs.

I've omitted all the `@[algebra]` attributes, as they are not used elsewhere.

The section `StrictWeakOrder` has been omitted, but I've left the mathport output in place.
Please delete if cleaning up.

I've commented out some classes which we think are completely unused in mathlib.

I've added many of the declarations to `nolints.json`.
If you clean up this file, please add documentation to classes that we are keeping.

Mario made the following analysis of uses in mathlib3:
* `is_symm_op`: unused except for some instances
* `is_commutative`: used a fair amount via some theorems about folds
  (also assuming `is_associative`)
* `is_associative`: ditto, also used in `noncomm_fold`
* `is_left_id`, `is_right_id`: unused except in the mathlib class `is_unital` and in `mono`
  (which looks like it could use `is_unital`)
* `is_left_null`, `is_right_null`: unused
* `is_left_cancel`, `is_right_cancel`: unused except for instances
* `is_idempotent`: this one is actually used to prove things not directly about `is_idempotent`
* `is_left_distrib`, `is_right_distrib`, `is_left_inv`, `is_right_inv`, `is_cond_left_inv`,
  `is_cond_right_inv`: unused
* `is_distinct`: unused (although we reinvented this one as `nontrivial`)
* `is_irrefl`, `is_refl`, `is_symm`, `is_trans`: significant usage
* `is_asymm`, `is_antisymm`, `is_total`, `is_strict_order`: a lot of uses but all in order theory
  and it's unclear how much could not be transferred to another typeclass
* `is_preorder`: unused except for instances
  (except `antisymmetrization`, maybe it could be transferred)
* `is_total_preorder`, `is_partial_order`: unused except for instances
* `is_linear_order`: unused except for instances
* `is_equiv`: unused except for instances (most uses can use `equivalence` instead)
* `is_per`: unused
* `is_incomp_trans`: unused
* `is_strict_weak_order`: significant usage (most of it on `rbmap`, could be transferred)
* `is_trichotomous`: some usage
* `is_strict_total_order`: looks like the only usage is in `rbmap` again
-/

set_option autoImplicit true

universe u v

-- Porting note: removed `outParam`
class IsSymmOp (α : Sort u) (β : Sort v) (op : α → α → β) : Prop where
  symm_op : ∀ a b, op a b = op b a
#align is_symm_op IsSymmOp

/-- A commutative binary operation. -/
@[deprecated Std.Commutative] -- 2024-02-02
abbrev IsCommutative (α : Sort u) (op : α → α → α) := Std.Commutative op
#align is_commutative Std.Commutative

instance (priority := 100) isSymmOp_of_isCommutative (α : Sort u) (op : α → α → α)
    [Std.Commutative op] : IsSymmOp α α op where symm_op := Std.Commutative.comm
#align is_symm_op_of_is_commutative isSymmOp_of_isCommutative

/-- An associative binary operation. -/
@[deprecated Std.Associative] -- 2024-02-02
abbrev IsAssociative (α : Sort u) (op : α → α → α) := Std.Associative op
#align is_associative Std.Associative

/-- A binary operation with a left identity. -/
@[deprecated Std.LawfulLeftIdentity] -- 2024-02-02
abbrev IsLeftId (α : Sort u) (op : α → α → α) (o : outParam α) := Std.LawfulLeftIdentity op o
#align is_left_id Std.LawfulLeftIdentity

/-- A binary operation with a right identity. -/
@[deprecated Std.LawfulRightIdentity] -- 2024-02-02
abbrev IsRightId (α : Sort u) (op : α → α → α) (o : outParam α) := Std.LawfulRightIdentity op o
#align is_right_id Std.LawfulRightIdentity

-- class IsLeftNull (α : Sort u) (op : α → α → α) (o : outParam α) : Prop where
--   left_null : ∀ a, op o a = o
#noalign is_left_null -- IsLeftNull

-- class IsRightNull (α : Sort u) (op : α → α → α) (o : outParam α) : Prop where
--   right_null : ∀ a, op a o = o
#noalign is_right_null -- IsRightNull

class IsLeftCancel (α : Sort u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c
#align is_left_cancel IsLeftCancel

class IsRightCancel (α : Sort u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c
#align is_right_cancel IsRightCancel

@[deprecated Std.IdempotentOp] -- 2024-02-02
abbrev IsIdempotent (α : Sort u) (op : α → α → α) := Std.IdempotentOp op
#align is_idempotent Std.IdempotentOp

-- class IsLeftDistrib (α : Sort u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
--   left_distrib : ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)
#noalign is_left_distrib -- IsLeftDistrib

-- class IsRightDistrib (α : Sort u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
--   right_distrib : ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)
#noalign is_right_distrib -- IsRightDistrib

-- class IsLeftInv (α : Sort u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) :
--     Prop where
--   left_inv : ∀ a, op (inv a) a = o
#noalign is_left_inv -- IsLeftInv

-- class IsRightInv (α : Sort u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) :
--     Prop where
--   right_inv : ∀ a, op a (inv a) = o
#noalign is_right_inv -- IsRightInv

-- class IsCondLeftInv (α : Sort u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
--     (p : outParam <| α → Prop) : Prop where
--   left_inv : ∀ a, p a → op (inv a) a = o
#noalign is_cond_left_inv -- IsCondLeftInv

-- class IsCondRightInv (α : Sort u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
--     (p : outParam <| α → Prop) : Prop where
--   right_inv : ∀ a, p a → op a (inv a) = o
#noalign is_cond_right_inv -- IsCondRightInv

-- class IsDistinct (α : Sort u) (a : α) (b : α) : Prop where
--   distinct : a ≠ b
#noalign is_distinct -- IsDistinct

/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Sort u) (β : Sort v) (f : α → β) (g : out β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Sort u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/

/-- `IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
class IsIrrefl (α : Sort u) (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a
#align is_irrefl IsIrrefl

/-- `IsRefl X r` means the binary relation `r` on `X` is reflexive. -/
class IsRefl (α : Sort u) (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a
#align is_refl IsRefl

/-- `IsSymm X r` means the binary relation `r` on `X` is symmetric. -/
class IsSymm (α : Sort u) (r : α → α → Prop) : Prop where
  symm : ∀ a b, r a b → r b a
#align is_symm IsSymm

/-- The opposite of a symmetric relation is symmetric. -/
instance (priority := 100) isSymmOp_of_isSymm (α : Sort u) (r : α → α → Prop) [IsSymm α r] :
    IsSymmOp α Prop r where symm_op a b := propext <| Iff.intro (IsSymm.symm a b) (IsSymm.symm b a)
#align is_symm_op_of_is_symm isSymmOp_of_isSymm

/-- `IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
class IsAsymm (α : Sort u) (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬r b a
#align is_asymm IsAsymm

/-- `IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
class IsAntisymm (α : Sort u) (r : α → α → Prop) : Prop where
  antisymm : ∀ a b, r a b → r b a → a = b
#align is_antisymm IsAntisymm

instance (priority := 100) IsAsymm.toIsAntisymm {α : Sort u} (r : α → α → Prop) [IsAsymm α r] :
    IsAntisymm α r where
  antisymm _ _ hx hy := (IsAsymm.asymm _ _ hx hy).elim

/-- `IsTrans X r` means the binary relation `r` on `X` is transitive. -/
class IsTrans (α : Sort u) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c
#align is_trans IsTrans

instance {α : Sort u} {r : α → α → Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩

instance (priority := 100) {α : Sort u} {r : α → α → Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩

/-- `IsTotal X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
class IsTotal (α : Sort u) (r : α → α → Prop) : Prop where
  total : ∀ a b, r a b ∨ r b a
#align is_total IsTotal

/-- `IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
class IsPreorder (α : Sort u) (r : α → α → Prop) extends IsRefl α r, IsTrans α r : Prop
#align is_preorder IsPreorder

/-- `IsTotalPreorder X r` means that the binary relation `r` on `X` is total and a preorder. -/
class IsTotalPreorder (α : Sort u) (r : α → α → Prop) extends IsTrans α r, IsTotal α r : Prop
#align is_total_preorder IsTotalPreorder

/-- Every total pre-order is a pre-order. -/
instance (priority := 100) isTotalPreorder_isPreorder (α : Sort u) (r : α → α → Prop)
    [s : IsTotalPreorder α r] : IsPreorder α r where
  trans := s.trans
  refl a := Or.elim (@IsTotal.total _ r _ a a) id id
#align is_total_preorder_is_preorder isTotalPreorder_isPreorder

/-- `IsPartialOrder X r` means that the binary relation `r` on `X` is a partial order, that is,
`IsPreorder X r` and `IsAntisymm X r`. -/
class IsPartialOrder (α : Sort u) (r : α → α → Prop) extends IsPreorder α r, IsAntisymm α r : Prop
#align is_partial_order IsPartialOrder

/-- `IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order, that is,
`IsPartialOrder X r` and `IsTotal X r`. -/
class IsLinearOrder (α : Sort u) (r : α → α → Prop) extends IsPartialOrder α r, IsTotal α r : Prop
#align is_linear_order IsLinearOrder

/-- `IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `IsPreorder X r` and `IsSymm X r`. -/
class IsEquiv (α : Sort u) (r : α → α → Prop) extends IsPreorder α r, IsSymm α r : Prop
#align is_equiv IsEquiv

-- /-- `IsPer X r` means that the binary relation `r` on `X` is a partial equivalence relation, that
-- is, `IsSymm X r` and `IsTrans X r`. -/
-- class IsPer (α : Sort u) (r : α → α → Prop) extends IsSymm α r, IsTrans α r : Prop
#noalign is_per -- IsPer

/-- `IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order, that is,
`IsIrrefl X r` and `IsTrans X r`. -/
class IsStrictOrder (α : Sort u) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r : Prop
#align is_strict_order IsStrictOrder

/-- `IsIncompTrans X lt` means that for `lt` a binary relation on `X`, the incomparable relation
`fun a b => ¬ lt a b ∧ ¬ lt b a` is transitive. -/
class IsIncompTrans (α : Sort u) (lt : α → α → Prop) : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a
#align is_incomp_trans IsIncompTrans

/-- `IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `IsStrictOrder X lt` and `IsIncompTrans X lt`. -/
class IsStrictWeakOrder (α : Sort u) (lt : α → α → Prop) extends IsStrictOrder α lt,
    IsIncompTrans α lt : Prop
#align is_strict_weak_order IsStrictWeakOrder

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
class IsTrichotomous (α : Sort u) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a
#align is_trichotomous IsTrichotomous

/-- `IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `IsTrichotomous X lt` and `IsStrictOrder X lt`. -/
class IsStrictTotalOrder (α : Sort u) (lt : α → α → Prop) extends IsTrichotomous α lt,
    IsStrictOrder α lt : Prop
#align is_strict_total_order IsStrictTotalOrder

/-- Equality is an equivalence relation. -/
instance eq_isEquiv (α : Sort u) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl
#align eq_is_equiv eq_isEquiv

section

variable {α : Sort u} {r : α → α → Prop}

local infixl:50 " ≺ " => r

theorem irrefl [IsIrrefl α r] (a : α) : ¬a ≺ a :=
  IsIrrefl.irrefl a
#align irrefl irrefl

theorem refl [IsRefl α r] (a : α) : a ≺ a :=
  IsRefl.refl a
#align refl refl

theorem trans [IsTrans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c :=
  IsTrans.trans _ _ _
#align trans trans

theorem symm [IsSymm α r] {a b : α} : a ≺ b → b ≺ a :=
  IsSymm.symm _ _
#align symm symm

theorem antisymm [IsAntisymm α r] {a b : α} : a ≺ b → b ≺ a → a = b :=
  IsAntisymm.antisymm _ _
#align antisymm antisymm

theorem asymm [IsAsymm α r] {a b : α} : a ≺ b → ¬b ≺ a :=
  IsAsymm.asymm _ _
#align asymm asymm

theorem trichotomous [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  IsTrichotomous.trichotomous
#align trichotomous trichotomous

theorem incomp_trans [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  IsIncompTrans.incomp_trans _ _ _
#align incomp_trans incomp_trans

instance (priority := 90) isAsymm_of_isTrans_of_isIrrefl [IsTrans α r] [IsIrrefl α r] :
    IsAsymm α r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩
#align is_asymm_of_is_trans_of_is_irrefl isAsymm_of_isTrans_of_isIrrefl

section ExplicitRelationVariants

variable (r)

@[elab_without_expected_type]
theorem irrefl_of [IsIrrefl α r] (a : α) : ¬a ≺ a :=
  irrefl a
#align irrefl_of irrefl_of

@[elab_without_expected_type]
theorem refl_of [IsRefl α r] (a : α) : a ≺ a :=
  refl a
#align refl_of refl_of

@[elab_without_expected_type]
theorem trans_of [IsTrans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c :=
  _root_.trans
#align trans_of trans_of

@[elab_without_expected_type]
theorem symm_of [IsSymm α r] {a b : α} : a ≺ b → b ≺ a :=
  symm
#align symm_of symm_of

@[elab_without_expected_type]
theorem asymm_of [IsAsymm α r] {a b : α} : a ≺ b → ¬b ≺ a :=
  asymm
#align asymm_of asymm_of

@[elab_without_expected_type]
theorem total_of [IsTotal α r] (a b : α) : a ≺ b ∨ b ≺ a :=
  IsTotal.total _ _
#align total_of total_of

@[elab_without_expected_type]
theorem trichotomous_of [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  trichotomous
#align trichotomous_of trichotomous_of

@[elab_without_expected_type]
theorem incomp_trans_of [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  incomp_trans
#align incomp_trans_of incomp_trans_of

end ExplicitRelationVariants

end

namespace StrictWeakOrder

section

variable {α : Sort u} {r : α → α → Prop}

local infixl:50 " ≺ " => r

def Equiv (a b : α) : Prop :=
  ¬a ≺ b ∧ ¬b ≺ a
#align strict_weak_order.equiv StrictWeakOrder.Equiv

variable [IsStrictWeakOrder α r]

local infixl:50 " ≈ " => @Equiv _ r

theorem erefl (a : α) : a ≈ a :=
  ⟨irrefl a, irrefl a⟩
#align strict_weak_order.erefl StrictWeakOrder.erefl

theorem esymm {a b : α} : a ≈ b → b ≈ a := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
#align strict_weak_order.esymm StrictWeakOrder.esymm

theorem etrans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
  incomp_trans
#align strict_weak_order.etrans StrictWeakOrder.etrans

theorem not_lt_of_equiv {a b : α} : a ≈ b → ¬a ≺ b := fun h => h.1
#align strict_weak_order.not_lt_of_equiv StrictWeakOrder.not_lt_of_equiv

theorem not_lt_of_equiv' {a b : α} : a ≈ b → ¬b ≺ a := fun h => h.2
#align strict_weak_order.not_lt_of_equiv' StrictWeakOrder.not_lt_of_equiv'

instance isEquiv : IsEquiv α (@Equiv _ r) where
  refl := erefl
  trans _ _ _ := etrans
  symm _ _ := esymm
#align strict_weak_order.is_equiv StrictWeakOrder.isEquiv

end

/-- The equivalence relation induced by `lt` -/
notation:50 a " ≈[" lt "]" b:50 => @Equiv _ lt a b--Equiv (r := lt) a b

end StrictWeakOrder

theorem isStrictWeakOrder_of_isTotalPreorder {α : Sort u} {le : α → α → Prop} {lt : α → α → Prop}
    [DecidableRel le] [IsTotalPreorder α le] (h : ∀ a b, lt a b ↔ ¬le b a) :
    IsStrictWeakOrder α lt :=
  { trans := fun a b c hab hbc =>
      have nba : ¬le b a := Iff.mp (h _ _) hab
      have ncb : ¬le c b := Iff.mp (h _ _) hbc
      have hab : le a b := Or.resolve_left (total_of le b a) nba
      have nca : ¬le c a := fun hca : le c a =>
        have hcb : le c b := trans_of le hca hab
        absurd hcb ncb
      Iff.mpr (h _ _) nca
    irrefl := fun a hlt => absurd (refl_of le a) (Iff.mp (h _ _) hlt)
    incomp_trans := fun a b c ⟨nab, nba⟩ ⟨nbc, ncb⟩ =>
      have hba : le b a := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nab)
      have hab : le a b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nba)
      have hcb : le c b := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) nbc)
      have hbc : le b c := Decidable.of_not_not (Iff.mp (not_congr (h _ _)) ncb)
      have hac : le a c := trans_of le hab hbc
      have hca : le c a := trans_of le hcb hba
      And.intro (fun n => absurd hca (Iff.mp (h _ _) n)) fun n => absurd hac (Iff.mp (h _ _) n) }
#align is_strict_weak_order_of_is_total_preorder isStrictWeakOrder_of_isTotalPreorder

theorem lt_of_lt_of_incomp {α : Sort u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, lt a b → ¬lt b c ∧ ¬lt c b → lt a c :=
  @fun a b c hab ⟨nbc, ncb⟩ =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hca hab) ncb
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt a b ∧ ¬lt b a := incomp_trans_of lt ⟨nac, nca⟩ ⟨ncb, nbc⟩
    absurd hab this.1
#align lt_of_lt_of_incomp lt_of_lt_of_incomp

theorem lt_of_incomp_of_lt {α : Sort u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, ¬lt a b ∧ ¬lt b a → lt b c → lt a c :=
  @fun a b c ⟨nab, nba⟩ hbc =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hbc hca) nba
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt b c ∧ ¬lt c b := incomp_trans_of lt ⟨nba, nab⟩ ⟨nac, nca⟩
    absurd hbc this.1
#align lt_of_incomp_of_lt lt_of_incomp_of_lt

theorem eq_of_incomp {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    ¬lt a b ∧ ¬lt b a → a = b := fun ⟨nab, nba⟩ =>
  match trichotomous_of lt a b with
  | Or.inl hab => absurd hab nab
  | Or.inr (Or.inl hab) => hab
  | Or.inr (Or.inr hba) => absurd hba nba
#align eq_of_incomp eq_of_incomp

theorem eq_of_eqv_lt {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    a ≈[lt]b → a = b :=
  eq_of_incomp
#align eq_of_eqv_lt eq_of_eqv_lt

theorem incomp_iff_eq {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    ¬lt a b ∧ ¬lt b a ↔ a = b :=
  Iff.intro eq_of_incomp fun hab => hab ▸ And.intro (irrefl_of lt a) (irrefl_of lt a)
#align incomp_iff_eq incomp_iff_eq

theorem eqv_lt_iff_eq {α : Sort u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    a ≈[lt]b ↔ a = b :=
  incomp_iff_eq a b
#align eqv_lt_iff_eq eqv_lt_iff_eq

theorem not_lt_of_lt {α : Sort u} {lt : α → α → Prop} [IsStrictOrder α lt] {a b} :
    lt a b → ¬lt b a := fun h₁ h₂ => absurd (trans_of lt h₁ h₂) (irrefl_of lt _)
#align not_lt_of_lt not_lt_of_lt
