/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import Mathlib.Logic.IsEmpty
import Mathlib.Logic.Relation
import Mathlib.Order.Basic

#align_import order.rel_classes from "leanprover-community/mathlib"@"7413128c3bcb3b0818e3e18720abc9ea3100fb49"

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in `Init.Algebra.Classes`. The main
difference between these classes and the usual order classes (`Preorder` etc) is that usual classes
extend `LE` and/or `LT` while these classes take a relation as an explicit argument.

-/


universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem of_eq [IsRefl α r] : ∀ {a b}, a = b → r a b
  | _, _, .refl _ => refl _
#align of_eq of_eq

theorem comm [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩
#align comm comm

theorem antisymm' [IsAntisymm α r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h
#align antisymm' antisymm'

theorem antisymm_iff [IsRefl α r] [IsAntisymm α r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩
#align antisymm_iff antisymm_iff

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
@[elab_without_expected_type]
theorem antisymm_of (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → a = b :=
  antisymm
#align antisymm_of antisymm_of

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
@[elab_without_expected_type]
theorem antisymm_of' (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → b = a :=
  antisymm'
#align antisymm_of' antisymm_of'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there.  -/
theorem comm_of (r : α → α → Prop) [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  comm
#align comm_of comm_of

theorem IsRefl.swap (r) [IsRefl α r] : IsRefl α (swap r) :=
  ⟨refl_of r⟩
#align is_refl.swap IsRefl.swap

theorem IsIrrefl.swap (r) [IsIrrefl α r] : IsIrrefl α (swap r) :=
  ⟨irrefl_of r⟩
#align is_irrefl.swap IsIrrefl.swap

theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun _ _ _ h₁ h₂ => trans_of r h₂ h₁⟩
#align is_trans.swap IsTrans.swap

theorem IsAntisymm.swap (r) [IsAntisymm α r] : IsAntisymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => _root_.antisymm h₂ h₁⟩
#align is_antisymm.swap IsAntisymm.swap

theorem IsAsymm.swap (r) [IsAsymm α r] : IsAsymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => asymm_of r h₂ h₁⟩
#align is_asymm.swap IsAsymm.swap

theorem IsTotal.swap (r) [IsTotal α r] : IsTotal α (swap r) :=
  ⟨fun a b => (total_of r a b).symm⟩
#align is_total.swap IsTotal.swap

theorem IsTrichotomous.swap (r) [IsTrichotomous α r] : IsTrichotomous α (swap r) :=
  ⟨fun a b => by simpa [Function.swap, or_comm, or_left_comm] using trichotomous_of r a b⟩
#align is_trichotomous.swap IsTrichotomous.swap

theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  { @IsRefl.swap α r _, @IsTrans.swap α r _ with }
#align is_preorder.swap IsPreorder.swap

theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { @IsIrrefl.swap α r _, @IsTrans.swap α r _ with }
#align is_strict_order.swap IsStrictOrder.swap

theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { @IsPreorder.swap α r _, @IsAntisymm.swap α r _ with }
#align is_partial_order.swap IsPartialOrder.swap

theorem IsTotalPreorder.swap (r) [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with }
#align is_total_preorder.swap IsTotalPreorder.swap

theorem IsLinearOrder.swap (r) [IsLinearOrder α r] : IsLinearOrder α (swap r) :=
  { @IsPartialOrder.swap α r _, @IsTotal.swap α r _ with }
#align is_linear_order.swap IsLinearOrder.swap

protected theorem IsAsymm.isAntisymm (r) [IsAsymm α r] : IsAntisymm α r :=
  ⟨fun _ _ h₁ h₂ => (_root_.asymm h₁ h₂).elim⟩
#align is_asymm.is_antisymm IsAsymm.isAntisymm

protected theorem IsAsymm.isIrrefl [IsAsymm α r] : IsIrrefl α r :=
  ⟨fun _ h => _root_.asymm h h⟩
#align is_asymm.is_irrefl IsAsymm.isIrrefl

protected theorem IsTotal.isTrichotomous (r) [IsTotal α r] : IsTrichotomous α r :=
  ⟨fun a b => or_left_comm.1 (Or.inr <| total_of r a b)⟩
#align is_total.is_trichotomous IsTotal.isTrichotomous

-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_isRefl (r) [IsTotal α r] : IsRefl α r :=
  ⟨fun a => or_self_iff.1 <| total_of r a a⟩

theorem ne_of_irrefl {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h
#align ne_of_irrefl ne_of_irrefl

theorem ne_of_irrefl' {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h
#align ne_of_irrefl' ne_of_irrefl'

theorem not_rel_of_subsingleton (r) [IsIrrefl α r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x
#align not_rel_of_subsingleton not_rel_of_subsingleton

theorem rel_of_subsingleton (r) [IsRefl α r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x
#align rel_of_subsingleton rel_of_subsingleton

@[simp]
theorem empty_relation_apply (a b : α) : EmptyRelation a b ↔ False :=
  Iff.rfl
#align empty_relation_apply empty_relation_apply

theorem eq_empty_relation (r) [IsIrrefl α r] [Subsingleton α] : r = EmptyRelation :=
  funext₂ <| by simpa using not_rel_of_subsingleton r
#align eq_empty_relation eq_empty_relation

instance : IsIrrefl α EmptyRelation :=
  ⟨fun _ => id⟩

theorem trans_trichotomous_left [IsTrans α r] [IsTrichotomous α r] {a b c : α} :
    ¬r b a → r b c → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  exacts [_root_.trans h₃ h₂, h₂, absurd h₃ h₁]
#align trans_trichotomous_left trans_trichotomous_left

theorem trans_trichotomous_right [IsTrans α r] [IsTrichotomous α r] {a b c : α} :
    r a b → ¬r c b → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  exacts [_root_.trans h₁ h₃, h₁, absurd h₃ h₂]
#align trans_trichotomous_right trans_trichotomous_right

theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := IsTrans.trans
#align transitive_of_trans transitive_of_trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [IsTrichotomous α r] [IsIrrefl α r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right <| mt (H _).1
    <| irrefl b
#align extensional_of_trichotomous_of_irrefl extensional_of_trichotomous_of_irrefl

/-- Construct a partial order from an `isStrictOrder` relation.

See note [reducible non-instances]. -/
abbrev partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where
  le x y := x = y ∨ r x y
  lt := r
  le_refl x := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (_root_.trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_le x y :=
    ⟨fun h => ⟨Or.inr h, not_or_of_not (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ <| e ▸ Or.inl rfl⟩
set_option linter.uppercaseLean3 false in
#align partial_order_of_SO partialOrderOfSO

/-- Construct a linear order from an `IsStrictTotalOrder` relation.

See note [reducible non-instances]. -/
abbrev linearOrderOfSTO (r) [IsStrictTotalOrder α r] [∀ x y, Decidable ¬r x y] : LinearOrder α :=
  let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y =>
      decidable_of_iff (¬r y x)
        ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
          h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | y, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    decidableLE := hD }
set_option linter.uppercaseLean3 false in
#align linear_order_of_STO linearOrderOfSTO

theorem IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) :=
  { IsTrichotomous.swap r, IsStrictOrder.swap r with }
#align is_strict_total_order.swap IsStrictTotalOrder.swap

/-! ### Order connection -/

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where
  /-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`. -/
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c
#align is_order_connected IsOrderConnected

theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c}
    (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c :=
  mt (IsOrderConnected.conn a b c) <| by simp [h₁, h₂]
#align is_order_connected.neg_trans IsOrderConnected.neg_trans

theorem isStrictWeakOrder_of_isOrderConnected [IsAsymm α r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @IsAsymm.isIrrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }
#align is_strict_weak_order_of_is_order_connected isStrictWeakOrder_of_isOrderConnected

-- see Note [lower instance priority]
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨fun _ _ _ h ↦ (trichotomous _ _).imp_right
    fun o ↦ o.elim (fun e ↦ e ▸ h) fun h' ↦ _root_.trans h' h⟩
#align is_order_connected_of_is_strict_total_order isStrictOrderConnected_of_isStrictTotalOrder

-- see Note [lower instance priority]
instance (priority := 100) isStrictTotalOrder_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsStrictWeakOrder α r :=
  { isStrictWeakOrder_of_isOrderConnected with }
#align is_strict_weak_order_of_is_strict_total_order isStrictTotalOrder_of_isStrictTotalOrder

/-! ### Well-order -/


/-- A well-founded relation. Not to be confused with `IsWellOrder`. -/
@[mk_iff] class IsWellFounded (α : Type u) (r : α → α → Prop) : Prop where
  /-- The relation is `WellFounded`, as a proposition. -/
  wf : WellFounded r
#align is_well_founded IsWellFounded
#align is_well_founded_iff isWellFounded_iff

#align has_well_founded WellFoundedRelation
set_option linter.uppercaseLean3 false in
#align has_well_founded.R WellFoundedRelation.rel

instance WellFoundedRelation.isWellFounded [h : WellFoundedRelation α] :
    IsWellFounded α WellFoundedRelation.rel :=
  { h with }

theorem WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : α} :
    WellFoundedRelation.rel a b → ¬ WellFoundedRelation.rel b a :=
  fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a

lemma WellFounded.prod_lex {ra : α → α → Prop} {rb : β → β → Prop} (ha : WellFounded ra)
    (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb) :=
  (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf
#align prod.lex_wf WellFounded.prod_lex

namespace IsWellFounded

variable (r) [IsWellFounded α r]

/-- Induction on a well-founded relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a :=
  wf.induction
#align is_well_founded.induction IsWellFounded.induction

/-- All values are accessible under the well-founded relation. -/
theorem apply : ∀ a, Acc r a :=
  wf.apply
#align is_well_founded.apply IsWellFounded.apply

/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `IsWellFounded.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, r y x → C y) → C x) → ∀ x : α, C x :=
  wf.fix
#align is_well_founded.fix IsWellFounded.fix

/-- The value from `IsWellFounded.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, r y x → C y) → C x) :
    ∀ x, fix r F x = F x fun y _ => fix r F y :=
  wf.fix_eq F
#align is_well_founded.fix_eq IsWellFounded.fix_eq

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  ⟨r, IsWellFounded.wf⟩

end IsWellFounded

theorem WellFounded.asymmetric {α : Sort*} {r : α → α → Prop} (h : WellFounded r) (a b) :
    r a b → ¬r b a :=
  @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _
#align well_founded.asymmetric WellFounded.asymmetric

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsAsymm α r :=
  ⟨IsWellFounded.wf.asymmetric⟩

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsIrrefl α r :=
  IsAsymm.isIrrefl

instance (r : α → α → Prop) [i : IsWellFounded α r] : IsWellFounded α (Relation.TransGen r) :=
  ⟨i.wf.transGen⟩

/-- A class for a well founded relation `<`. -/
abbrev WellFoundedLT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· < ·)
#align well_founded_lt WellFoundedLT

/-- A class for a well founded relation `>`. -/
abbrev WellFoundedGT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· > ·)
#align well_founded_gt WellFoundedGT

lemma wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α (· < ·) := IsWellFounded.wf
lemma wellFounded_gt [LT α] [WellFoundedGT α] : @WellFounded α (· > ·) := IsWellFounded.wf

-- See note [lower instance priority]
instance (priority := 100) (α : Type*) [LT α] [h : WellFoundedLT α] : WellFoundedGT αᵒᵈ :=
  h

-- See note [lower instance priority]
instance (priority := 100) (α : Type*) [LT α] [h : WellFoundedGT α] : WellFoundedLT αᵒᵈ :=
  h

theorem wellFoundedGT_dual_iff (α : Type*) [LT α] : WellFoundedGT αᵒᵈ ↔ WellFoundedLT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩
#align well_founded_gt_dual_iff wellFoundedGT_dual_iff

theorem wellFoundedLT_dual_iff (α : Type*) [LT α] : WellFoundedLT αᵒᵈ ↔ WellFoundedGT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩
#align well_founded_lt_dual_iff wellFoundedLT_dual_iff

/-- A well order is a well-founded linear order. -/
class IsWellOrder (α : Type u) (r : α → α → Prop) extends
  IsTrichotomous α r, IsTrans α r, IsWellFounded α r : Prop
#align is_well_order IsWellOrder

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r where

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrichotomous α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrans α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsIrrefl α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] : IsAsymm α r := by
  infer_instance

namespace WellFoundedLT

variable [LT α] [WellFoundedLT α]

/-- Inducts on a well-founded `<` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, y < x → C y) → C x) → C a :=
  IsWellFounded.induction _
#align well_founded_lt.induction WellFoundedLT.induction

/-- All values are accessible under the well-founded `<`. -/
theorem apply : ∀ a : α, Acc (· < ·) a :=
  IsWellFounded.apply _
#align well_founded_lt.apply WellFoundedLT.apply

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLT.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, y < x → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· < ·)
#align well_founded_lt.fix WellFoundedLT.fix

/-- The value from `WellFoundedLT.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, y < x → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F
#align well_founded_lt.fix_eq WellFoundedLT.fix_eq

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLT` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLT

namespace WellFoundedGT

variable [LT α] [WellFoundedGT α]

/-- Inducts on a well-founded `>` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, x < y → C y) → C x) → C a :=
  IsWellFounded.induction _
#align well_founded_gt.induction WellFoundedGT.induction

/-- All values are accessible under the well-founded `>`. -/
theorem apply : ∀ a : α, Acc (· > ·) a :=
  IsWellFounded.apply _
#align well_founded_gt.apply WellFoundedGT.apply

/-- Creates data, given a way to generate a value from all that compare as greater. See also
`WellFoundedGT.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, x < y → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· > ·)
#align well_founded_gt.fix WellFoundedGT.fix

/-- The value from `WellFoundedGT.fix` is built from the successive ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, x < y → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F
#align well_founded_gt.fix_eq WellFoundedGT.fix_eq

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedGT` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· > ·)

end WellFoundedGT

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrder α :=
  letI := fun x y => Classical.dec ¬r x y
  linearOrderOfSTO r
#align is_well_order.linear_order IsWellOrder.linearOrder

/-- Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance. -/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf
#align is_well_order.to_has_well_founded IsWellOrder.toHasWellFounded

-- This isn't made into an instance as it loops with `IsIrrefl α r`.
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α → α → Prop) [hr : IsIrrefl α r] :
    IsWellOrder α r :=
  { hr with
    trichotomous := fun a b => Or.inr <| Or.inl <| Subsingleton.elim a b,
    trans := fun a b _ h => (not_rel_of_subsingleton r a b h).elim,
    wf := ⟨fun a => ⟨_, fun y h => (not_rel_of_subsingleton r y a h).elim⟩⟩ }
#align subsingleton.is_well_order Subsingleton.isWellOrder

instance [Subsingleton α] : IsWellOrder α EmptyRelation :=
  Subsingleton.isWellOrder _

instance (priority := 100) [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  trichotomous := isEmptyElim
  trans := isEmptyElim
  wf := wellFounded_of_isEmpty r

instance [IsWellFounded α r] [IsWellFounded β s] : IsWellFounded (α × β) (Prod.Lex r s) :=
  ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩

instance [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ =>
    match @trichotomous _ r _ a₁ b₁ with
    | Or.inl h₁ => Or.inl <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inr h₁) => Or.inr <| Or.inr <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inl (.refl _)) =>
        match @trichotomous _ s _ a₂ b₂ with
        | Or.inl h => Or.inl <| Prod.Lex.right _ h
        | Or.inr (Or.inr h) => Or.inr <| Or.inr <| Prod.Lex.right _ h
        | Or.inr (Or.inl (.refl _)) => Or.inr <| Or.inl rfl
  trans a b c h₁ h₂ := by
    cases' h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab <;> cases' h₂ with _ _ c₁ c₂ bc _ _ c₂ bc
    exacts [.left _ _ (_root_.trans ab bc), .left _ _ ab, .left _ _ bc,
      .right _ (_root_.trans ab bc)]

instance (r : α → α → Prop) [IsWellFounded α r] (f : β → α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩

instance (f : α → ℕ) : IsWellFounded _ (InvImage (· < ·) f) :=
  ⟨(measure f).wf⟩

theorem Subrelation.isWellFounded (r : α → α → Prop) [IsWellFounded α r] {s : α → α → Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩
#align subrelation.is_well_founded Subrelation.isWellFounded

instance Prod.wellFoundedLT [PartialOrder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β] :
    WellFoundedLT (α × β) where
  wf := by
    refine @Subrelation.wf (α × β) (Prod.Lex (· < ·) (· < ·)) (· < ·) ?_ IsWellFounded.wf
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ w
    simp only [Prod.mk_lt_mk] at w
    rcases eq_or_ne a₁ a₂ with rfl | ha
    · right
      simpa using w
    · left
      rcases w with ⟨a_lt, _⟩ | ⟨a_le, _⟩
      · assumption
      · exact Ne.lt_of_le ha a_le

instance Prod.wellFoundedGT [PartialOrder α] [WellFoundedGT α] [Preorder β] [WellFoundedGT β] :
    WellFoundedGT (α × β) :=
  @Prod.wellFoundedLT αᵒᵈ βᵒᵈ _ _ _ _

namespace Set

/-- An unbounded or cofinal set. -/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, ¬r b a
#align set.unbounded Set.Unbounded

/-- A bounded or final set. Not to be confused with `Bornology.IsBounded`. -/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀ b ∈ s, r b a
#align set.bounded Set.Bounded

@[simp]
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop, not_and, not_not]
#align set.not_bounded_iff Set.not_bounded_iff

@[simp]
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm, not_bounded_iff]
#align set.not_unbounded_iff Set.not_unbounded_iff

theorem unbounded_of_isEmpty [IsEmpty α] {r : α → α → Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim
#align set.unbounded_of_is_empty Set.unbounded_of_isEmpty

end Set

namespace Order.Preimage

instance instIsRefl {r : α → α → Prop} [IsRefl α r] {f : β → α} : IsRefl β (f ⁻¹'o r) :=
  ⟨fun a => refl_of r (f a)⟩

instance instIsTrans {r : α → α → Prop} [IsTrans α r] {f : β → α} : IsTrans β (f ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

end Order.Preimage

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `Preorder.lt_iff_le_not_le`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
class IsNonstrictStrictOrder (α : Type*) (r : semiOutParam (α → α → Prop)) (s : α → α → Prop) :
    Prop where
  /-- The relation `r` is the nonstrict relation corresponding to the strict relation `s`. -/
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a
#align is_nonstrict_strict_order IsNonstrictStrictOrder

theorem right_iff_left_not_left {r s : α → α → Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _
#align right_iff_left_not_left right_iff_left_not_left

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
theorem right_iff_left_not_left_of (r s : α → α → Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left
#align right_iff_left_not_left_of right_iff_left_not_left_of

instance {s : α → α → Prop} [IsNonstrictStrictOrder α r s] : IsIrrefl α s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section Subset
variable [HasSubset α] {a b c : α}

lemma subset_of_eq_of_subset (hab : a = b) (hbc : b ⊆ c) : a ⊆ c := by rwa [hab]
#align subset_of_eq_of_subset subset_of_eq_of_subset

lemma subset_of_subset_of_eq (hab : a ⊆ b) (hbc : b = c) : a ⊆ c := by rwa [← hbc]
#align subset_of_subset_of_eq subset_of_subset_of_eq

@[refl]
lemma subset_refl [IsRefl α (· ⊆ ·)] (a : α) : a ⊆ a := refl _
#align subset_refl subset_refl

lemma subset_rfl [IsRefl α (· ⊆ ·)] : a ⊆ a := refl _
#align subset_rfl subset_rfl

lemma subset_of_eq [IsRefl α (· ⊆ ·)] : a = b → a ⊆ b := fun h => h ▸ subset_rfl
#align subset_of_eq subset_of_eq

lemma superset_of_eq [IsRefl α (· ⊆ ·)] : a = b → b ⊆ a := fun h => h ▸ subset_rfl
#align superset_of_eq superset_of_eq

lemma ne_of_not_subset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → a ≠ b := mt subset_of_eq
#align ne_of_not_subset ne_of_not_subset

lemma ne_of_not_superset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → b ≠ a := mt superset_of_eq
#align ne_of_not_superset ne_of_not_superset

@[trans]
lemma subset_trans [IsTrans α (· ⊆ ·)] {a b c : α} : a ⊆ b → b ⊆ c → a ⊆ c := _root_.trans
#align subset_trans subset_trans

lemma subset_antisymm [IsAntisymm α (· ⊆ ·)] : a ⊆ b → b ⊆ a → a = b := antisymm
#align subset_antisymm subset_antisymm

lemma superset_antisymm [IsAntisymm α (· ⊆ ·)] : a ⊆ b → b ⊆ a → b = a := antisymm'
#align superset_antisymm superset_antisymm

alias Eq.trans_subset := subset_of_eq_of_subset
#align eq.trans_subset Eq.trans_subset

alias HasSubset.subset.trans_eq := subset_of_subset_of_eq
#align has_subset.subset.trans_eq HasSubset.subset.trans_eq

alias Eq.subset' := subset_of_eq --TODO: Fix it and kill `Eq.subset`
#align eq.subset' Eq.subset'

alias Eq.superset := superset_of_eq
#align eq.superset Eq.superset

alias HasSubset.Subset.trans := subset_trans
#align has_subset.subset.trans HasSubset.Subset.trans

alias HasSubset.Subset.antisymm := subset_antisymm
#align has_subset.subset.antisymm HasSubset.Subset.antisymm

alias HasSubset.Subset.antisymm' := superset_antisymm
#align has_subset.subset.antisymm' HasSubset.Subset.antisymm'

theorem subset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun h => ⟨h.subset', h.superset⟩, fun h => h.1.antisymm h.2⟩
#align subset_antisymm_iff subset_antisymm_iff

theorem superset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ b ⊆ a ∧ a ⊆ b :=
  ⟨fun h => ⟨h.superset, h.subset'⟩, fun h => h.1.antisymm' h.2⟩
#align superset_antisymm_iff superset_antisymm_iff

end Subset

section Ssubset
variable [HasSSubset α] {a b c : α}

lemma ssubset_of_eq_of_ssubset (hab : a = b) (hbc : b ⊂ c) : a ⊂ c := by rwa [hab]
#align ssubset_of_eq_of_ssubset ssubset_of_eq_of_ssubset

lemma ssubset_of_ssubset_of_eq (hab : a ⊂ b) (hbc : b = c) : a ⊂ c := by rwa [← hbc]
#align ssubset_of_ssubset_of_eq ssubset_of_ssubset_of_eq

lemma ssubset_irrefl [IsIrrefl α (· ⊂ ·)] (a : α) : ¬a ⊂ a := irrefl _
#align ssubset_irrefl ssubset_irrefl

lemma ssubset_irrfl [IsIrrefl α (· ⊂ ·)] {a : α} : ¬a ⊂ a := irrefl _
#align ssubset_irrfl ssubset_irrfl

lemma ne_of_ssubset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → a ≠ b := ne_of_irrefl
#align ne_of_ssubset ne_of_ssubset

lemma ne_of_ssuperset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → b ≠ a := ne_of_irrefl'
#align ne_of_ssuperset ne_of_ssuperset

@[trans]
lemma ssubset_trans [IsTrans α (· ⊂ ·)] {a b c : α} : a ⊂ b → b ⊂ c → a ⊂ c := _root_.trans
#align ssubset_trans ssubset_trans

lemma ssubset_asymm [IsAsymm α (· ⊂ ·)] {a b : α} : a ⊂ b → ¬b ⊂ a := asymm
#align ssubset_asymm ssubset_asymm

alias Eq.trans_ssubset := ssubset_of_eq_of_ssubset
#align eq.trans_ssubset Eq.trans_ssubset

alias HasSSubset.SSubset.trans_eq := ssubset_of_ssubset_of_eq
#align has_ssubset.ssubset.trans_eq HasSSubset.SSubset.trans_eq

alias HasSSubset.SSubset.false := ssubset_irrfl
#align has_ssubset.ssubset.false HasSSubset.SSubset.false

alias HasSSubset.SSubset.ne := ne_of_ssubset
#align has_ssubset.ssubset.ne HasSSubset.SSubset.ne

alias HasSSubset.SSubset.ne' := ne_of_ssuperset
#align has_ssubset.ssubset.ne' HasSSubset.SSubset.ne'

alias HasSSubset.SSubset.trans := ssubset_trans
#align has_ssubset.ssubset.trans HasSSubset.SSubset.trans

alias HasSSubset.SSubset.asymm := ssubset_asymm
#align has_ssubset.ssubset.asymm HasSSubset.SSubset.asymm

end Ssubset

section SubsetSsubset

variable [HasSubset α] [HasSSubset α] [IsNonstrictStrictOrder α (· ⊆ ·) (· ⊂ ·)] {a b c : α}

theorem ssubset_iff_subset_not_subset : a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a :=
  right_iff_left_not_left
#align ssubset_iff_subset_not_subset ssubset_iff_subset_not_subset

theorem subset_of_ssubset (h : a ⊂ b) : a ⊆ b :=
  (ssubset_iff_subset_not_subset.1 h).1
#align subset_of_ssubset subset_of_ssubset

theorem not_subset_of_ssubset (h : a ⊂ b) : ¬b ⊆ a :=
  (ssubset_iff_subset_not_subset.1 h).2
#align not_subset_of_ssubset not_subset_of_ssubset

theorem not_ssubset_of_subset (h : a ⊆ b) : ¬b ⊂ a := fun h' => not_subset_of_ssubset h' h
#align not_ssubset_of_subset not_ssubset_of_subset

theorem ssubset_of_subset_not_subset (h₁ : a ⊆ b) (h₂ : ¬b ⊆ a) : a ⊂ b :=
  ssubset_iff_subset_not_subset.2 ⟨h₁, h₂⟩
#align ssubset_of_subset_not_subset ssubset_of_subset_not_subset

alias HasSSubset.SSubset.subset := subset_of_ssubset
#align has_ssubset.ssubset.subset HasSSubset.SSubset.subset

alias HasSSubset.SSubset.not_subset := not_subset_of_ssubset
#align has_ssubset.ssubset.not_subset HasSSubset.SSubset.not_subset

alias HasSubset.Subset.not_ssubset := not_ssubset_of_subset
#align has_subset.subset.not_ssubset HasSubset.Subset.not_ssubset

alias HasSubset.Subset.ssubset_of_not_subset := ssubset_of_subset_not_subset
#align has_subset.subset.ssubset_of_not_subset HasSubset.Subset.ssubset_of_not_subset

theorem ssubset_of_subset_of_ssubset [IsTrans α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : b ⊂ c) : a ⊂ c :=
  (h₁.trans h₂.subset).ssubset_of_not_subset fun h => h₂.not_subset <| h.trans h₁
#align ssubset_of_subset_of_ssubset ssubset_of_subset_of_ssubset

theorem ssubset_of_ssubset_of_subset [IsTrans α (· ⊆ ·)] (h₁ : a ⊂ b) (h₂ : b ⊆ c) : a ⊂ c :=
  (h₁.subset.trans h₂).ssubset_of_not_subset fun h => h₁.not_subset <| h₂.trans h
#align ssubset_of_ssubset_of_subset ssubset_of_ssubset_of_subset

theorem ssubset_of_subset_of_ne [IsAntisymm α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : a ≠ b) : a ⊂ b :=
  h₁.ssubset_of_not_subset <| mt h₁.antisymm h₂
#align ssubset_of_subset_of_ne ssubset_of_subset_of_ne

theorem ssubset_of_ne_of_subset [IsAntisymm α (· ⊆ ·)] (h₁ : a ≠ b) (h₂ : a ⊆ b) : a ⊂ b :=
  ssubset_of_subset_of_ne h₂ h₁
#align ssubset_of_ne_of_subset ssubset_of_ne_of_subset

theorem eq_or_ssubset_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a = b ∨ a ⊂ b :=
  (em (b ⊆ a)).imp h.antisymm h.ssubset_of_not_subset
#align eq_or_ssubset_of_subset eq_or_ssubset_of_subset

theorem ssubset_or_eq_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a ⊂ b ∨ a = b :=
  (eq_or_ssubset_of_subset h).symm
#align ssubset_or_eq_of_subset ssubset_or_eq_of_subset

lemma eq_of_subset_of_not_ssubset [IsAntisymm α (· ⊆ ·)] (hab : a ⊆ b) (hba : ¬ a ⊂ b) : a = b :=
  (eq_or_ssubset_of_subset hab).resolve_right hba

lemma eq_of_superset_of_not_ssuperset [IsAntisymm α (· ⊆ ·)] (hab : a ⊆ b) (hba : ¬ a ⊂ b) :
    b = a := ((eq_or_ssubset_of_subset hab).resolve_right hba).symm

alias HasSubset.Subset.trans_ssubset := ssubset_of_subset_of_ssubset
#align has_subset.subset.trans_ssubset HasSubset.Subset.trans_ssubset

alias HasSSubset.SSubset.trans_subset := ssubset_of_ssubset_of_subset
#align has_ssubset.ssubset.trans_subset HasSSubset.SSubset.trans_subset

alias HasSubset.Subset.ssubset_of_ne := ssubset_of_subset_of_ne
#align has_subset.subset.ssubset_of_ne HasSubset.Subset.ssubset_of_ne

alias Ne.ssubset_of_subset := ssubset_of_ne_of_subset
#align ne.ssubset_of_subset Ne.ssubset_of_subset

alias HasSubset.Subset.eq_or_ssubset := eq_or_ssubset_of_subset
#align has_subset.subset.eq_or_ssubset HasSubset.Subset.eq_or_ssubset

alias HasSubset.Subset.ssubset_or_eq := ssubset_or_eq_of_subset
#align has_subset.subset.ssubset_or_eq HasSubset.Subset.ssubset_or_eq

alias HasSubset.Subset.eq_of_not_ssubset := eq_of_subset_of_not_ssubset
alias HasSubset.Subset.eq_of_not_ssuperset := eq_of_superset_of_not_ssuperset

theorem ssubset_iff_subset_ne [IsAntisymm α (· ⊆ ·)] : a ⊂ b ↔ a ⊆ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.subset, h.ne⟩, fun h => h.1.ssubset_of_ne h.2⟩
#align ssubset_iff_subset_ne ssubset_iff_subset_ne

theorem subset_iff_ssubset_or_eq [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] :
    a ⊆ b ↔ a ⊂ b ∨ a = b :=
  ⟨fun h => h.ssubset_or_eq, fun h => h.elim subset_of_ssubset subset_of_eq⟩
#align subset_iff_ssubset_or_eq subset_iff_ssubset_or_eq

end SubsetSsubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


instance [Preorder α] : IsRefl α (· ≤ ·) :=
  ⟨le_refl⟩

instance [Preorder α] : IsRefl α (· ≥ ·) :=
  IsRefl.swap _

instance [Preorder α] : IsTrans α (· ≤ ·) :=
  ⟨@le_trans _ _⟩

instance [Preorder α] : IsTrans α (· ≥ ·) :=
  IsTrans.swap _

instance [Preorder α] : IsPreorder α (· ≤ ·) where

instance [Preorder α] : IsPreorder α (· ≥ ·) where

instance [Preorder α] : IsIrrefl α (· < ·) :=
  ⟨lt_irrefl⟩

instance [Preorder α] : IsIrrefl α (· > ·) :=
  IsIrrefl.swap _

instance [Preorder α] : IsTrans α (· < ·) :=
  ⟨@lt_trans _ _⟩

instance [Preorder α] : IsTrans α (· > ·) :=
  IsTrans.swap _

instance [Preorder α] : IsAsymm α (· < ·) :=
  ⟨@lt_asymm _ _⟩

instance [Preorder α] : IsAsymm α (· > ·) :=
  IsAsymm.swap _

instance [Preorder α] : IsAntisymm α (· < ·) :=
  IsAsymm.isAntisymm _

instance [Preorder α] : IsAntisymm α (· > ·) :=
  IsAsymm.isAntisymm _

instance [Preorder α] : IsStrictOrder α (· < ·) where

instance [Preorder α] : IsStrictOrder α (· > ·) where

instance [Preorder α] : IsNonstrictStrictOrder α (· ≤ ·) (· < ·) :=
  ⟨@lt_iff_le_not_le _ _⟩

instance [PartialOrder α] : IsAntisymm α (· ≤ ·) :=
  ⟨@le_antisymm _ _⟩

instance [PartialOrder α] : IsAntisymm α (· ≥ ·) :=
  IsAntisymm.swap _

instance [PartialOrder α] : IsPartialOrder α (· ≤ ·) where

instance [PartialOrder α] : IsPartialOrder α (· ≥ ·) where

instance LE.isTotal [LinearOrder α] : IsTotal α (· ≤ ·) :=
  ⟨le_total⟩

instance [LinearOrder α] : IsTotal α (· ≥ ·) :=
  IsTotal.swap _

-- Porting note: this was `by infer_instance` before
instance [LinearOrder α] : IsTotalPreorder α (· ≤ ·) where

instance [LinearOrder α] : IsTotalPreorder α (· ≥ ·) where

instance [LinearOrder α] : IsLinearOrder α (· ≤ ·) where

instance [LinearOrder α] : IsLinearOrder α (· ≥ ·) where

instance [LinearOrder α] : IsTrichotomous α (· < ·) :=
  ⟨lt_trichotomy⟩

instance [LinearOrder α] : IsTrichotomous α (· > ·) :=
  IsTrichotomous.swap _

instance [LinearOrder α] : IsTrichotomous α (· ≤ ·) :=
  IsTotal.isTrichotomous _

instance [LinearOrder α] : IsTrichotomous α (· ≥ ·) :=
  IsTotal.isTrichotomous _

instance [LinearOrder α] : IsStrictTotalOrder α (· < ·) where

instance [LinearOrder α] : IsOrderConnected α (· < ·) := by infer_instance

instance [LinearOrder α] : IsIncompTrans α (· < ·) := by infer_instance

instance [LinearOrder α] : IsStrictWeakOrder α (· < ·) := by infer_instance

theorem transitive_le [Preorder α] : Transitive (@LE.le α _) :=
  transitive_of_trans _
#align transitive_le transitive_le

theorem transitive_lt [Preorder α] : Transitive (@LT.lt α _) :=
  transitive_of_trans _
#align transitive_lt transitive_lt

theorem transitive_ge [Preorder α] : Transitive (@GE.ge α _) :=
  transitive_of_trans _
#align transitive_ge transitive_ge

theorem transitive_gt [Preorder α] : Transitive (@GT.gt α _) :=
  transitive_of_trans _
#align transitive_gt transitive_gt

instance OrderDual.isTotal_le [LE α] [h : IsTotal α (· ≤ ·)] : IsTotal αᵒᵈ (· ≤ ·) :=
  @IsTotal.swap α _ h

instance : WellFoundedLT ℕ :=
  ⟨Nat.lt_wfRel.wf⟩
#align nat.lt_wf Nat.lt_wfRel

instance [LinearOrder α] [h : IsWellOrder α (· < ·)] : IsWellOrder αᵒᵈ (· > ·) := h

instance [LinearOrder α] [h : IsWellOrder α (· > ·)] : IsWellOrder αᵒᵈ (· < ·) := h
