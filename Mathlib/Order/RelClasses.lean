/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Logic.IsEmpty
import Mathlib.Order.Basic
import Mathlib.Tactic.MkIffOfInductiveProp
import Batteries.WF

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Order/Defs/Unbundled.lean`.
The main difference between these classes and the usual order classes (`Preorder` etc) is that
usual classes extend `LE` and/or `LT` while these classes take a relation as an explicit argument.
-/

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem IsRefl.swap (r) [IsRefl α r] : IsRefl α (swap r) :=
  ⟨refl_of r⟩

theorem IsIrrefl.swap (r) [IsIrrefl α r] : IsIrrefl α (swap r) :=
  ⟨irrefl_of r⟩

theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun _ _ _ h₁ h₂ => trans_of r h₂ h₁⟩

theorem IsAntisymm.swap (r) [IsAntisymm α r] : IsAntisymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => _root_.antisymm h₂ h₁⟩

theorem IsAsymm.swap (r) [IsAsymm α r] : IsAsymm α (swap r) :=
  ⟨fun _ _ h₁ h₂ => asymm_of r h₂ h₁⟩

theorem IsTotal.swap (r) [IsTotal α r] : IsTotal α (swap r) :=
  ⟨fun a b => (total_of r a b).symm⟩

theorem IsTrichotomous.swap (r) [IsTrichotomous α r] : IsTrichotomous α (swap r) :=
  ⟨fun a b => by simpa [Function.swap, or_comm, or_left_comm] using trichotomous_of r a b⟩

theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  { @IsRefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { @IsIrrefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { @IsPreorder.swap α r _, @IsAntisymm.swap α r _ with }

theorem eq_empty_relation (r) [IsIrrefl α r] [Subsingleton α] : r = EmptyRelation :=
  funext₂ <| by simpa using not_rel_of_subsingleton r

/-- Construct a partial order from an `isStrictOrder` relation.

See note [reducible non-instances]. -/
abbrev partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where
  le x y := x = y ∨ r x y
  lt := r
  le_refl _ := Or.inl rfl
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
  lt_iff_le_not_ge x y :=
    ⟨fun h => ⟨Or.inr h, not_or_intro (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ <| e ▸ Or.inl rfl⟩

/-- Construct a linear order from an `IsStrictTotalOrder` relation.

See note [reducible non-instances]. -/
abbrev linearOrderOfSTO (r) [IsStrictTotalOrder α r] [DecidableRel r] : LinearOrder α :=
  let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y => decidable_of_iff (¬r y x)
    ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
      h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | _, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := hD }

theorem IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) :=
  { IsTrichotomous.swap r, IsStrictOrder.swap r with }

/-! ### Order connection -/

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`. -/
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where
  /-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`. -/
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c

theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c}
    (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c :=
  mt (IsOrderConnected.conn a b c) <| by simp [h₁, h₂]

theorem isStrictWeakOrder_of_isOrderConnected [IsAsymm α r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @IsAsymm.isIrrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

-- see Note [lower instance priority]
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨fun _ _ _ h ↦ (trichotomous _ _).imp_right
    fun o ↦ o.elim (fun e ↦ e ▸ h) fun h' ↦ _root_.trans h' h⟩

/-! ### Inverse Image -/

theorem InvImage.isTrichotomous [IsTrichotomous α r] {f : β → α} (h : Function.Injective f) :
    IsTrichotomous β (InvImage r f)  where
  trichotomous a b := trichotomous (f a) (f b) |>.imp3 id (h ·) id

instance InvImage.isAsymm [IsAsymm α r] (f : β → α) : IsAsymm β (InvImage r f) where
  asymm a b h h2 := IsAsymm.asymm (f a) (f b) h h2

/-! ### Well-order -/


/-- A well-founded relation. Not to be confused with `IsWellOrder`. -/
@[mk_iff] class IsWellFounded (α : Type u) (r : α → α → Prop) : Prop where
  /-- The relation is `WellFounded`, as a proposition. -/
  wf : WellFounded r

instance WellFoundedRelation.isWellFounded [h : WellFoundedRelation α] :
    IsWellFounded α WellFoundedRelation.rel :=
  { h with }

theorem WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : α} :
    WellFoundedRelation.rel a b → ¬ WellFoundedRelation.rel b a :=
  fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a

theorem WellFoundedRelation.asymmetric₃ {α : Sort*} [WellFoundedRelation α] {a b c : α} :
    WellFoundedRelation.rel a b → WellFoundedRelation.rel b c → ¬ WellFoundedRelation.rel c a :=
  fun hab hbc hca => WellFoundedRelation.asymmetric₃ hca hab hbc
termination_by a

lemma WellFounded.prod_lex {ra : α → α → Prop} {rb : β → β → Prop} (ha : WellFounded ra)
    (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb) :=
  (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf

section PSigma

open PSigma

/-- The lexicographical order of well-founded relations is well-founded. -/
theorem WellFounded.psigma_lex
    {α : Sort*} {β : α → Sort*} {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}
    (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b

theorem WellFounded.psigma_revLex
    {α : Sort*} {β : Sort*} {r : α → α → Prop} {s : β → β → Prop}
    (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a

theorem WellFounded.psigma_skipLeft (α : Type u) {β : Type v} {s : β → β → Prop}
    (hb : WellFounded s) : WellFounded (SkipLeft α s) :=
  psigma_revLex emptyWf.wf hb

end PSigma

namespace IsWellFounded

variable (r) [IsWellFounded α r]

/-- Induction on a well-founded relation. -/
theorem induction {C : α → Prop} (a : α) (ind : ∀ x, (∀ y, r y x → C y) → C x) : C a :=
  wf.induction _ ind

/-- All values are accessible under the well-founded relation. -/
theorem apply : ∀ a, Acc r a :=
  wf.apply

/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `IsWellFounded.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, r y x → C y) → C x) → ∀ x : α, C x :=
  wf.fix

/-- The value from `IsWellFounded.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, r y x → C y) → C x) :
    ∀ x, fix r F x = F x fun y _ => fix r F y :=
  wf.fix_eq F

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  ⟨r, IsWellFounded.wf⟩

end IsWellFounded

theorem WellFounded.asymmetric {α : Sort*} {r : α → α → Prop} (h : WellFounded r) (a b) :
    r a b → ¬r b a :=
  @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _

theorem WellFounded.asymmetric₃ {α : Sort*} {r : α → α → Prop} (h : WellFounded r) (a b c) :
    r a b → r b c → ¬r c a :=
  @WellFoundedRelation.asymmetric₃ _ ⟨_, h⟩ _ _ _

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsAsymm α r :=
  ⟨IsWellFounded.wf.asymmetric⟩

-- see Note [lower instance priority]
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : IsIrrefl α r :=
  IsAsymm.isIrrefl

instance (r : α → α → Prop) [i : IsWellFounded α r] : IsWellFounded α (Relation.TransGen r) :=
  ⟨i.wf.transGen⟩

/-- A class for a well-founded relation `<`. -/
abbrev WellFoundedLT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· < ·)

/-- A class for a well-founded relation `>`. -/
abbrev WellFoundedGT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· > ·)

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

theorem wellFoundedLT_dual_iff (α : Type*) [LT α] : WellFoundedLT αᵒᵈ ↔ WellFoundedGT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
class IsWellOrder (α : Type u) (r : α → α → Prop) : Prop
    extends IsTrichotomous α r, IsTrans α r, IsWellFounded α r

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
theorem induction {C : α → Prop} (a : α) (ind : ∀ x, (∀ y, y < x → C y) → C x) : C a :=
  IsWellFounded.induction _ _ ind

/-- All values are accessible under the well-founded `<`. -/
theorem apply : ∀ a : α, Acc (· < ·) a :=
  IsWellFounded.apply _

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLT.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, y < x → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· < ·)

/-- The value from `WellFoundedLT.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, y < x → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLT` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLT

namespace WellFoundedGT

variable [LT α] [WellFoundedGT α]

/-- Inducts on a well-founded `>` relation. -/
theorem induction {C : α → Prop} (a : α) (ind : ∀ x, (∀ y, x < y → C y) → C x) : C a :=
  IsWellFounded.induction _ _ ind

/-- All values are accessible under the well-founded `>`. -/
theorem apply : ∀ a : α, Acc (· > ·) a :=
  IsWellFounded.apply _

/-- Creates data, given a way to generate a value from all that compare as greater. See also
`WellFoundedGT.fix_eq`. -/
def fix {C : α → Sort*} : (∀ x : α, (∀ y : α, x < y → C y) → C x) → ∀ x : α, C x :=
  IsWellFounded.fix (· > ·)

/-- The value from `WellFoundedGT.fix` is built from the successive ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : ∀ x : α, (∀ y : α, x < y → C y) → C x) :
    ∀ x, fix F x = F x fun y _ => fix F y :=
  IsWellFounded.fix_eq _ F

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedGT` instance. -/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· > ·)

end WellFoundedGT

open Classical in
/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrder α :=
  linearOrderOfSTO r

/-- Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance. -/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `IsIrrefl α r`.
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α → α → Prop) [hr : IsIrrefl α r] :
    IsWellOrder α r :=
  { hr with
    trichotomous := fun a b => Or.inr <| Or.inl <| Subsingleton.elim a b,
    trans := fun a b _ h => (not_rel_of_subsingleton r a b h).elim,
    wf := ⟨fun a => ⟨_, fun y h => (not_rel_of_subsingleton r y a h).elim⟩⟩ }

instance [Subsingleton α] : IsWellOrder α EmptyRelation :=
  Subsingleton.isWellOrder _

instance (priority := 100) [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  trichotomous := isEmptyElim
  trans := isEmptyElim
  wf := wellFounded_of_isEmpty r

instance Prod.Lex.instIsWellFounded [IsWellFounded α r] [IsWellFounded β s] :
    IsWellFounded (α × β) (Prod.Lex r s) :=
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
    rcases h₁ with ⟨a₂, b₂, ab⟩ | ⟨a₁, ab⟩ <;> rcases h₂ with ⟨c₁, c₂, bc⟩ | ⟨c₂, bc⟩
    exacts [.left _ _ (_root_.trans ab bc), .left _ _ ab, .left _ _ bc,
      .right _ (_root_.trans ab bc)]

instance (r : α → α → Prop) [IsWellFounded α r] (f : β → α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩

instance (f : α → ℕ) : IsWellFounded _ (InvImage (· < ·) f) :=
  ⟨(measure f).wf⟩

theorem Subrelation.isWellFounded (r : α → α → Prop) [IsWellFounded α r] {s : α → α → Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩

/-- See `Prod.wellFoundedLT` for a version that only requires `Preorder α`. -/
theorem Prod.wellFoundedLT' [PartialOrder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β] :
    WellFoundedLT (α × β) :=
  Subrelation.isWellFounded (Prod.Lex (· < ·) (· < ·))
    fun {x y} h ↦ (Prod.lt_iff.mp h).elim (fun h ↦ .left _ _ h.1)
    fun h ↦ h.1.lt_or_eq.elim (.left _ _) <| by cases x; cases y; rintro rfl; exact .right _ h.2

/-- See `Prod.wellFoundedGT` for a version that only requires `Preorder α`. -/
theorem Prod.wellFoundedGT' [PartialOrder α] [WellFoundedGT α] [Preorder β] [WellFoundedGT β] :
    WellFoundedGT (α × β) :=
  @Prod.wellFoundedLT' αᵒᵈ βᵒᵈ _ _ _ _

namespace Set

/-- An unbounded or cofinal set. -/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, ¬r b a

/-- A bounded or final set. Not to be confused with `Bornology.IsBounded`. -/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀ b ∈ s, r b a

@[simp]
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop]

@[simp]
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm, not_bounded_iff]

theorem unbounded_of_isEmpty [IsEmpty α] {r : α → α → Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim

end Set

namespace Order.Preimage

instance instIsRefl [IsRefl α r] {f : β → α} : IsRefl β (f ⁻¹'o r) :=
  ⟨fun _ => refl_of r _⟩

instance instIsIrrefl [IsIrrefl α r] {f : β → α} : IsIrrefl β (f ⁻¹'o r) :=
  ⟨fun _ => irrefl_of r _⟩

instance instIsSymm [IsSymm α r] {f : β → α} : IsSymm β (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ symm_of r⟩

instance instIsAsymm [IsAsymm α r] {f : β → α} : IsAsymm β (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ asymm_of r⟩

instance instIsTrans [IsTrans α r] {f : β → α} : IsTrans β (f ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

instance instIsPreorder [IsPreorder α r] {f : β → α} : IsPreorder β (f ⁻¹'o r) where

instance instIsStrictOrder [IsStrictOrder α r] {f : β → α} : IsStrictOrder β (f ⁻¹'o r) where

instance instIsStrictWeakOrder [IsStrictWeakOrder α r] {f : β → α} :
    IsStrictWeakOrder β (f ⁻¹'o r) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

instance instIsEquiv [IsEquiv α r] {f : β → α} : IsEquiv β (f ⁻¹'o r) where

instance instIsTotal [IsTotal α r] {f : β → α} : IsTotal β (f ⁻¹'o r) :=
  ⟨fun _ _ => total_of r _ _⟩

theorem isAntisymm [IsAntisymm α r] {f : β → α} (hf : f.Injective) :
    IsAntisymm β (f ⁻¹'o r) :=
  ⟨fun _ _ h₁ h₂ ↦ hf <| antisymm_of r h₁ h₂⟩

end Order.Preimage

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `Preorder.lt_iff_le_not_ge`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
class IsNonstrictStrictOrder (α : Type*) (r : semiOutParam (α → α → Prop)) (s : α → α → Prop) :
    Prop where
  /-- The relation `r` is the nonstrict relation corresponding to the strict relation `s`. -/
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a

theorem right_iff_left_not_left {r s : α → α → Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
theorem right_iff_left_not_left_of (r s : α → α → Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left

instance {s : α → α → Prop} [IsNonstrictStrictOrder α r s] : IsIrrefl α s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section Subset
variable [HasSubset α] {a b c : α}

lemma subset_of_eq_of_subset (hab : a = b) (hbc : b ⊆ c) : a ⊆ c := by rwa [hab]

lemma subset_of_subset_of_eq (hab : a ⊆ b) (hbc : b = c) : a ⊆ c := by rwa [← hbc]

@[refl, simp]
lemma subset_refl [IsRefl α (· ⊆ ·)] (a : α) : a ⊆ a := refl _

lemma subset_rfl [IsRefl α (· ⊆ ·)] : a ⊆ a := refl _

lemma subset_of_eq [IsRefl α (· ⊆ ·)] : a = b → a ⊆ b := fun h => h ▸ subset_rfl

lemma superset_of_eq [IsRefl α (· ⊆ ·)] : a = b → b ⊆ a := fun h => h ▸ subset_rfl

lemma ne_of_not_subset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → a ≠ b := mt subset_of_eq

lemma ne_of_not_superset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → b ≠ a := mt superset_of_eq

@[trans]
lemma subset_trans [IsTrans α (· ⊆ ·)] {a b c : α} : a ⊆ b → b ⊆ c → a ⊆ c := _root_.trans

lemma subset_antisymm [IsAntisymm α (· ⊆ ·)] : a ⊆ b → b ⊆ a → a = b := antisymm

lemma superset_antisymm [IsAntisymm α (· ⊆ ·)] : a ⊆ b → b ⊆ a → b = a := antisymm'

alias Eq.trans_subset := subset_of_eq_of_subset

alias HasSubset.subset.trans_eq := subset_of_subset_of_eq

alias Eq.subset' := subset_of_eq --TODO: Fix it and kill `Eq.subset`

alias Eq.superset := superset_of_eq

alias HasSubset.Subset.trans := subset_trans

alias HasSubset.Subset.antisymm := subset_antisymm

alias HasSubset.Subset.antisymm' := superset_antisymm

theorem subset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun h => ⟨h.subset', h.superset⟩, fun h => h.1.antisymm h.2⟩

theorem superset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ b ⊆ a ∧ a ⊆ b :=
  ⟨fun h => ⟨h.superset, h.subset'⟩, fun h => h.1.antisymm' h.2⟩

end Subset

section Ssubset
variable [HasSSubset α] {a b c : α}

lemma ssubset_of_eq_of_ssubset (hab : a = b) (hbc : b ⊂ c) : a ⊂ c := by rwa [hab]

lemma ssubset_of_ssubset_of_eq (hab : a ⊂ b) (hbc : b = c) : a ⊂ c := by rwa [← hbc]

lemma ssubset_irrefl [IsIrrefl α (· ⊂ ·)] (a : α) : ¬a ⊂ a := irrefl _

lemma ssubset_irrfl [IsIrrefl α (· ⊂ ·)] {a : α} : ¬a ⊂ a := irrefl _

lemma ne_of_ssubset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → a ≠ b := ne_of_irrefl

lemma ne_of_ssuperset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → b ≠ a := ne_of_irrefl'

@[trans]
lemma ssubset_trans [IsTrans α (· ⊂ ·)] {a b c : α} : a ⊂ b → b ⊂ c → a ⊂ c := _root_.trans

lemma ssubset_asymm [IsAsymm α (· ⊂ ·)] {a b : α} : a ⊂ b → ¬b ⊂ a := asymm

alias Eq.trans_ssubset := ssubset_of_eq_of_ssubset

alias HasSSubset.SSubset.trans_eq := ssubset_of_ssubset_of_eq

alias HasSSubset.SSubset.false := ssubset_irrfl

alias HasSSubset.SSubset.ne := ne_of_ssubset

alias HasSSubset.SSubset.ne' := ne_of_ssuperset

alias HasSSubset.SSubset.trans := ssubset_trans

alias HasSSubset.SSubset.asymm := ssubset_asymm

end Ssubset

section SubsetSsubset

variable [HasSubset α] [HasSSubset α] [IsNonstrictStrictOrder α (· ⊆ ·) (· ⊂ ·)] {a b c : α}

theorem ssubset_iff_subset_not_subset : a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a :=
  right_iff_left_not_left

theorem subset_of_ssubset (h : a ⊂ b) : a ⊆ b :=
  (ssubset_iff_subset_not_subset.1 h).1

theorem not_subset_of_ssubset (h : a ⊂ b) : ¬b ⊆ a :=
  (ssubset_iff_subset_not_subset.1 h).2

theorem not_ssubset_of_subset (h : a ⊆ b) : ¬b ⊂ a := fun h' => not_subset_of_ssubset h' h

theorem ssubset_of_subset_not_subset (h₁ : a ⊆ b) (h₂ : ¬b ⊆ a) : a ⊂ b :=
  ssubset_iff_subset_not_subset.2 ⟨h₁, h₂⟩

alias HasSSubset.SSubset.subset := subset_of_ssubset

alias HasSSubset.SSubset.not_subset := not_subset_of_ssubset

alias HasSubset.Subset.not_ssubset := not_ssubset_of_subset

alias HasSubset.Subset.ssubset_of_not_subset := ssubset_of_subset_not_subset

theorem ssubset_of_subset_of_ssubset [IsTrans α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : b ⊂ c) : a ⊂ c :=
  (h₁.trans h₂.subset).ssubset_of_not_subset fun h => h₂.not_subset <| h.trans h₁

theorem ssubset_of_ssubset_of_subset [IsTrans α (· ⊆ ·)] (h₁ : a ⊂ b) (h₂ : b ⊆ c) : a ⊂ c :=
  (h₁.subset.trans h₂).ssubset_of_not_subset fun h => h₁.not_subset <| h₂.trans h

theorem ssubset_of_subset_of_ne [IsAntisymm α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : a ≠ b) : a ⊂ b :=
  h₁.ssubset_of_not_subset <| mt h₁.antisymm h₂

theorem ssubset_of_ne_of_subset [IsAntisymm α (· ⊆ ·)] (h₁ : a ≠ b) (h₂ : a ⊆ b) : a ⊂ b :=
  ssubset_of_subset_of_ne h₂ h₁

theorem eq_or_ssubset_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a = b ∨ a ⊂ b :=
  (em (b ⊆ a)).imp h.antisymm h.ssubset_of_not_subset

theorem ssubset_or_eq_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a ⊂ b ∨ a = b :=
  (eq_or_ssubset_of_subset h).symm

lemma eq_of_subset_of_not_ssubset [IsAntisymm α (· ⊆ ·)] (hab : a ⊆ b) (hba : ¬ a ⊂ b) : a = b :=
  (eq_or_ssubset_of_subset hab).resolve_right hba

lemma eq_of_superset_of_not_ssuperset [IsAntisymm α (· ⊆ ·)] (hab : a ⊆ b) (hba : ¬ a ⊂ b) :
    b = a := ((eq_or_ssubset_of_subset hab).resolve_right hba).symm

alias HasSubset.Subset.trans_ssubset := ssubset_of_subset_of_ssubset

alias HasSSubset.SSubset.trans_subset := ssubset_of_ssubset_of_subset

alias HasSubset.Subset.ssubset_of_ne := ssubset_of_subset_of_ne

alias Ne.ssubset_of_subset := ssubset_of_ne_of_subset

alias HasSubset.Subset.eq_or_ssubset := eq_or_ssubset_of_subset

alias HasSubset.Subset.ssubset_or_eq := ssubset_or_eq_of_subset

alias HasSubset.Subset.eq_of_not_ssubset := eq_of_subset_of_not_ssubset
alias HasSubset.Subset.eq_of_not_ssuperset := eq_of_superset_of_not_ssuperset

theorem ssubset_iff_subset_ne [IsAntisymm α (· ⊆ ·)] : a ⊂ b ↔ a ⊆ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.subset, h.ne⟩, fun h => h.1.ssubset_of_ne h.2⟩

theorem subset_iff_ssubset_or_eq [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] :
    a ⊆ b ↔ a ⊂ b ∨ a = b :=
  ⟨fun h => h.ssubset_or_eq, fun h => h.elim subset_of_ssubset subset_of_eq⟩

namespace GCongr

variable [IsTrans α (· ⊆ ·)] {a b c d : α}

@[gcongr]
theorem ssubset_imp_ssubset (h₁ : c ⊆ a) (h₂ : b ⊆ d) : a ⊂ b → c ⊂ d :=
  fun h => (h₁.trans_ssubset h).trans_subset h₂

@[gcongr]
theorem ssuperset_imp_ssuperset (h₁ : a ⊆ c) (h₂ : d ⊆ b) : a ⊃ b → c ⊃ d :=
  ssubset_imp_ssubset h₂ h₁

/-- See if the term is `a ⊂ b` and the goal is `a ⊆ b`. -/
@[gcongr_forward] def exactSubsetOfSSubset : Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``subset_of_ssubset #[h])

end GCongr

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
  ⟨@lt_iff_le_not_ge _ _⟩

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

theorem transitive_le [Preorder α] : Transitive (@LE.le α _) :=
  transitive_of_trans _

theorem transitive_lt [Preorder α] : Transitive (@LT.lt α _) :=
  transitive_of_trans _

theorem transitive_ge [Preorder α] : Transitive (@GE.ge α _) :=
  transitive_of_trans _

theorem transitive_gt [Preorder α] : Transitive (@GT.gt α _) :=
  transitive_of_trans _

instance OrderDual.isTotal_le [LE α] [h : IsTotal α (· ≤ ·)] : IsTotal αᵒᵈ (· ≤ ·) :=
  @IsTotal.swap α _ h

instance : WellFoundedLT ℕ :=
  ⟨Nat.lt_wfRel.wf⟩

instance (priority := 100) isWellOrder_lt [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder α (· < ·) where

instance (priority := 100) isWellOrder_gt [LinearOrder α] [WellFoundedGT α] :
    IsWellOrder α (· > ·) where
