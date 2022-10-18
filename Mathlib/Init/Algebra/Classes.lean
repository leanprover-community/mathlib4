/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Logic

/-!
# Unbundled algebra classes

These classes and the `@[algebra]` attribute are part of an incomplete refactor described
[here on the github Wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1).

By themselves, these classes are not good replacements for the `monoid` / `group` etc structures
provided by mathlib, as they are not discoverable by `simp` unlike the current lemmas due to there
being little to index on. The Wiki page linked above describes an algebraic normalizer,
but it is not implemented.

## Porting notes:
This file is ancient, and it would be good to replace it with a clean version
that provides what mathlib4 actually needs.

I've omitted all the `@[algebra]` attributes, as they are not used elsewhere.

The section `StrictWeakOrder` has been omitted, but I've left the mathport output in place.
Please delete if cleaning up.
-/

universe u v

-- @[algebra]
class IsSymmOp (α : Type u) (β : outParam (Type v)) (op : outParam (α → α → β)) : Prop where
  symm_op : ∀ a b, op a b = op b a

-- @[algebra]
class IsCommutative (α : Type u) (op : α → α → α) : Prop where
  comm : ∀ a b, op a b = op b a

instance (priority := 100) is_symm_op_of_is_commutative (α : Type u) (op : α → α → α)
    [IsCommutative α op] : IsSymmOp α α op where symm_op :=
  IsCommutative.comm

-- @[algebra]
class IsAssociative (α : Type u) (op : α → α → α) : Prop where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)

-- @[algebra]
class IsLeftId (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  left_id : ∀ a, op o a = a

-- @[algebra]
class IsRightId (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  right_id : ∀ a, op a o = a

-- @[algebra]
class IsLeftNull (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  left_null : ∀ a, op o a = o

-- @[algebra]
class IsRightNull (α : Type u) (op : α → α → α) (o : outParam α) : Prop where
  right_null : ∀ a, op a o = o

-- @[algebra]
class IsLeftCancel (α : Type u) (op : α → α → α) : Prop where
  left_cancel : ∀ a b c, op a b = op a c → b = c

-- @[algebra]
class IsRightCancel (α : Type u) (op : α → α → α) : Prop where
  right_cancel : ∀ a b c, op a b = op c b → a = c

-- @[algebra]
class IsIdempotent (α : Type u) (op : α → α → α) : Prop where
  idempotent : ∀ a, op a a = a

-- @[algebra]
class IsLeftDistrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
  left_distrib : ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)

-- @[algebra]
class IsRightDistrib (α : Type u) (op₁ : α → α → α) (op₂ : outParam <| α → α → α) : Prop where
  right_distrib : ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)

-- @[algebra]
class IsLeftInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) : Prop
   where
  left_inv : ∀ a, op (inv a) a = o

-- @[algebra]
class IsRightInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α) : Prop
    where
  right_inv : ∀ a, op a (inv a) = o

-- @[algebra]
class IsCondLeftInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
  (p : outParam <| α → Prop) : Prop where
  left_inv : ∀ a, p a → op (inv a) a = o

-- @[algebra]
class IsCondRightInv (α : Type u) (op : α → α → α) (inv : outParam <| α → α) (o : outParam α)
  (p : outParam <| α → Prop) : Prop where
  right_inv : ∀ a, p a → op a (inv a) = o

-- @[algebra]
class IsDistinct (α : Type u) (a : α) (b : α) : Prop where
  distinct : a ≠ b

/-
-- The following type class doesn't seem very useful, a regular simp lemma should work for this.
class is_inv (α : Type u) (β : Type v) (f : α → β) (g : out β → α) : Prop :=
(inv : ∀ a, g (f a) = a)

-- The following one can also be handled using a regular simp lemma
class is_idempotent (α : Type u) (f : α → α) : Prop :=
(idempotent : ∀ a, f (f a) = f a)
-/
/-- `is_irrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
-- @[algebra]
class IsIrrefl (α : Type u) (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬r a a

/-- `is_refl X r` means the binary relation `r` on `X` is reflexive. -/
-- @[algebra]
class IsRefl (α : Type u) (r : α → α → Prop) : Prop where
  refl : ∀ a, r a a

/-- `is_symm X r` means the binary relation `r` on `X` is symmetric. -/
-- @[algebra]
class IsSymm (α : Type u) (r : α → α → Prop) : Prop where
  symm : ∀ a b, r a b → r b a

/-- The opposite of a symmetric relation is symmetric. -/
instance (priority := 100) is_symm_op_of_is_symm (α : Type u) (r : α → α → Prop) [IsSymm α r] :
    IsSymmOp α Prop r where
  symm_op := fun a b => propext <| Iff.intro (IsSymm.symm a b) (IsSymm.symm b a)

/-- `is_asymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
-- @[algebra]
class IsAsymm (α : Type u) (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬r b a

/-- `is_antisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
-- @[algebra]
class IsAntisymm (α : Type u) (r : α → α → Prop) : Prop where
  antisymm : ∀ a b, r a b → r b a → a = b

/-- `is_trans X r` means the binary relation `r` on `X` is transitive. -/
-- @[algebra]
class IsTrans (α : Type u) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c

/-- `is_total X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`.-/
-- @[algebra]
class IsTotal (α : Type u) (r : α → α → Prop) : Prop where
  total : ∀ a b, r a b ∨ r b a

/-- `is_preorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
-- @[algebra]
class IsPreorder (α : Type u) (r : α → α → Prop) extends IsRefl α r, IsTrans α r : Prop

/-- `is_total_preorder X r` means that the binary relation `r` on `X` is total and a preorder. -/
-- @[algebra]
class IsTotalPreorder (α : Type u) (r : α → α → Prop) extends IsTrans α r, IsTotal α r : Prop

/-- Every total pre-order is a pre-order. -/
instance is_total_preorder_is_preorder (α : Type u) (r : α → α → Prop) [s : IsTotalPreorder α r] :
    IsPreorder α r where
  trans := s.trans
  refl := fun a => Or.elim (@IsTotal.total _ r _ a a) id id

/-- `is_partial_order X r` means that the binary relation `r` on `X` is a partial order, that is,
`is_preorder X r` and `is_antisymm X r`. -/
-- @[algebra]
class IsPartialOrder (α : Type u) (r : α → α → Prop) extends IsPreorder α r, IsAntisymm α r : Prop

/-- `is_linear_order X r` means that the binary relation `r` on `X` is a linear order, that is,
`is_partial_order X r` and `is_total X r`. -/
-- @[algebra]
class IsLinearOrder (α : Type u) (r : α → α → Prop) extends IsPartialOrder α r, IsTotal α r : Prop

/-- `is_equiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `is_preorder X r` and `is_symm X r`. -/
-- @[algebra]
class IsEquiv (α : Type u) (r : α → α → Prop) extends IsPreorder α r, IsSymm α r : Prop

/-- `is_per X r` means that the binary relation `r` on `X` is a partial equivalence relation, that
is, `is_symm X r` and `is_trans X r`. -/
-- @[algebra]
class IsPer (α : Type u) (r : α → α → Prop) extends IsSymm α r, IsTrans α r : Prop

/-- `is_strict_order X r` means that the binary relation `r` on `X` is a strict order, that is,
`is_irrefl X r` and `is_trans X r`. -/
-- @[algebra]
class IsStrictOrder (α : Type u) (r : α → α → Prop) extends IsIrrefl α r, IsTrans α r : Prop

/-- `is_incomp_trans X lt` means that for `lt` a binary relation on `X`, the incomparable relation
`λ a b, ¬ lt a b ∧ ¬ lt b a` is transitive. -/
-- @[algebra]
class IsIncompTrans (α : Type u) (lt : α → α → Prop) : Prop where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

/-- `is_strict_weak_order X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `is_strict_order X lt` and `is_incomp_trans X lt`. -/
-- @[algebra]
class IsStrictWeakOrder (α : Type u) (lt : α → α → Prop)
  extends IsStrictOrder α lt, IsIncompTrans α lt : Prop

/-- `is_trichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
-- @[algebra]
class IsTrichotomous (α : Type u) (lt : α → α → Prop) : Prop where
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a

/-- `is_strict_total_order X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `is_trichotomous X lt` and `is_strict_order X lt`. -/
-- @[algebra]
class IsStrictTotalOrder (α : Type u) (lt : α → α → Prop)
  extends IsTrichotomous α lt, IsStrictOrder α lt : Prop

/-- Equality is an equivalence relation. -/
instance eq_is_equiv (α : Type u) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

section

variable {α : Type u} {r : α → α → Prop}

/-- Temporary notation for a relation. -/
local infixl:50 "≺" => r

theorem irrefl [IsIrrefl α r] (a : α) : ¬a ≺ a :=
  IsIrrefl.irrefl a

theorem refl [IsRefl α r] (a : α) : a ≺ a :=
  IsRefl.refl a

theorem trans [IsTrans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c :=
  IsTrans.trans _ _ _

theorem symm [IsSymm α r] {a b : α} : a ≺ b → b ≺ a :=
  IsSymm.symm _ _

theorem antisymm [IsAntisymm α r] {a b : α} : a ≺ b → b ≺ a → a = b :=
  IsAntisymm.antisymm _ _

theorem asymm [IsAsymm α r] {a b : α} : a ≺ b → ¬b ≺ a :=
  IsAsymm.asymm _ _

theorem trichotomous [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  IsTrichotomous.trichotomous

theorem incomp_trans [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  IsIncompTrans.incomp_trans _ _ _

instance (priority := 90) is_asymm_of_is_trans_of_is_irrefl [IsTrans α r] [IsIrrefl α r] :
    IsAsymm α r :=
  ⟨fun a _ h₁ h₂ => absurd (trans h₁ h₂) (irrefl a)⟩

section ExplicitRelationVariants

variable (r)

@[elabWithoutExpectedType]
theorem irrefl_of [IsIrrefl α r] (a : α) : ¬a ≺ a :=
  irrefl a

@[elabWithoutExpectedType]
theorem refl_of [IsRefl α r] (a : α) : a ≺ a :=
  refl a

@[elabWithoutExpectedType]
theorem trans_of [IsTrans α r] {a b c : α} : a ≺ b → b ≺ c → a ≺ c :=
  trans

@[elabWithoutExpectedType]
theorem symm_of [IsSymm α r] {a b : α} : a ≺ b → b ≺ a :=
  symm

@[elabWithoutExpectedType]
theorem asymm_of [IsAsymm α r] {a b : α} : a ≺ b → ¬b ≺ a :=
  asymm

@[elabWithoutExpectedType]
theorem total_of [IsTotal α r] (a b : α) : a ≺ b ∨ b ≺ a :=
  IsTotal.total _ _

@[elabWithoutExpectedType]
theorem trichotomous_of [IsTrichotomous α r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  trichotomous

@[elabWithoutExpectedType]
theorem incomp_trans_of [IsIncompTrans α r] {a b c : α} :
    ¬a ≺ b ∧ ¬b ≺ a → ¬b ≺ c ∧ ¬c ≺ b → ¬a ≺ c ∧ ¬c ≺ a :=
  incomp_trans

end ExplicitRelationVariants

end

-- Porting note: the `StrictWeakOrder` section has been ommitted.

-- namespace StrictWeakOrder

-- section

-- parameter {α : Type u}{r : α → α → Prop}

-- -- mathport name: «expr ≺ »
-- local infixl:50 "≺" => r

-- def Equiv (a b : α) : Prop :=
--   ¬a ≺ b ∧ ¬b ≺ a

-- parameter [IsStrictWeakOrder α r]

-- -- mathport name: equiv
-- local infixl:50 " ≈ " => equiv

-- theorem erefl (a : α) : a ≈ a :=
--   ⟨irrefl a, irrefl a⟩

-- theorem esymm {a b : α} : a ≈ b → b ≈ a := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

-- theorem etrans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
--   incomp_trans

-- theorem not_lt_of_equiv {a b : α} : a ≈ b → ¬a ≺ b := fun h => h.1

-- theorem not_lt_of_equiv' {a b : α} : a ≈ b → ¬b ≺ a := fun h => h.2

-- instance is_equiv : IsEquiv α equiv where
--   refl := erefl
--   trans := @etrans
--   symm := @esymm

-- end

-- -- mathport name: «expr ≈[ ] »
-- notation:50 -- Notation for the equivalence relation induced by lt
-- a " ≈[" lt "]" b:50 => @Equiv _ lt a b

-- end StrictWeakOrder

theorem is_strict_weak_order_of_is_total_preorder {α : Type u} {le : α → α → Prop}
    {lt : α → α → Prop} [DecidableRel le] [IsTotalPreorder α le] (h : ∀ a b, lt a b ↔ ¬le b a) :
    IsStrictWeakOrder α lt :=
  { trans := fun a b c hab hbc =>
      have nba : ¬le b a := Iff.mp (h _ _) hab
      have ncb : ¬le c b := Iff.mp (h _ _) hbc
      have hab : le a b := Or.resolve_left (total_of le b a) nba
      have nca : ¬le c a := fun hca : le c a =>
        have hcb : le c b := trans_of le hca hab
        absurd hcb ncb
      Iff.mpr (h _ _) nca,
    irrefl := fun a hlt => absurd (refl_of le a) (Iff.mp (h _ _) hlt),
    incomp_trans := fun a b c ⟨nab, nba⟩ ⟨nbc, ncb⟩ =>
      have hba : le b a := Decidable.of_not_not (Iff.mp (not_iff_not_of_iff (h _ _)) nab)
      have hab : le a b := Decidable.of_not_not (Iff.mp (not_iff_not_of_iff (h _ _)) nba)
      have hcb : le c b := Decidable.of_not_not (Iff.mp (not_iff_not_of_iff (h _ _)) nbc)
      have hbc : le b c := Decidable.of_not_not (Iff.mp (not_iff_not_of_iff (h _ _)) ncb)
      have hac : le a c := trans_of le hab hbc
      have hca : le c a := trans_of le hcb hba
      And.intro (fun n => absurd hca (Iff.mp (h _ _) n)) fun n => absurd hac (Iff.mp (h _ _) n) }

theorem lt_of_lt_of_incomp {α : Type u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, lt a b → ¬lt b c ∧ ¬lt c b → lt a c :=
  @fun a b c hab ⟨nbc, ncb⟩ =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hca hab) ncb
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt a b ∧ ¬lt b a := incomp_trans_of lt ⟨nac, nca⟩ ⟨ncb, nbc⟩
    absurd hab this.1

theorem lt_of_incomp_of_lt {α : Type u} {lt : α → α → Prop} [IsStrictWeakOrder α lt]
    [DecidableRel lt] : ∀ {a b c}, ¬lt a b ∧ ¬lt b a → lt b c → lt a c :=
  @fun a b c ⟨nab, nba⟩ hbc =>
  have nca : ¬lt c a := fun hca => absurd (trans_of lt hbc hca) nba
  Decidable.by_contradiction fun nac : ¬lt a c =>
    have : ¬lt b c ∧ ¬lt c b := incomp_trans_of lt ⟨nba, nab⟩ ⟨nac, nca⟩
    absurd hbc this.1

theorem eq_of_incomp {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    ¬lt a b ∧ ¬lt b a → a = b :=
  fun ⟨nab, nba⟩ =>
  match trichotomous_of lt a b with
  | Or.inl hab => absurd hab nab
  | Or.inr (Or.inl hab) => hab
  | Or.inr (Or.inr hba) => absurd hba nba

theorem eq_of_eqv_lt {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] {a b} :
    ¬lt a b ∧ ¬lt b a → a = b :=
  eq_of_incomp

theorem incomp_iff_eq {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    ¬lt a b ∧ ¬lt b a ↔ a = b :=
  Iff.intro eq_of_incomp fun hab => by
    rw [hab]
    exact ⟨irrefl_of lt b, irrefl_of lt b⟩

theorem eqv_lt_iff_eq {α : Type u} {lt : α → α → Prop} [IsTrichotomous α lt] [IsIrrefl α lt] (a b) :
    ¬lt a b ∧ ¬lt b a ↔ a = b :=
  incomp_iff_eq a b

theorem not_lt_of_lt {α : Type u} {lt : α → α → Prop} [IsStrictOrder α lt] {a b} :
    lt a b → ¬lt b a :=
  fun h₁ h₂ => absurd (trans_of lt h₁ h₂) (irrefl_of lt _)
