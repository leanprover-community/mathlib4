/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Order.OrderDual
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Order/Defs/Unbundled.lean`.
The main difference between these classes and the usual order classes (`Preorder` etc) is that
usual classes extend `LE` and/or `LT` while these classes take a relation as an explicit argument.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem Std.Refl.swap (r : α → α → Prop) [Std.Refl r] : Std.Refl (swap r) :=
  ⟨refl_of r⟩

@[deprecated (since := "2026-01-09")] alias IsRefl.swap := Std.Refl.swap

theorem Std.Irrefl.swap (r : α → α → Prop) [Std.Irrefl r] : Std.Irrefl (swap r) :=
  ⟨irrefl_of r⟩

theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun _ _ _ h₁ h₂ => trans_of r h₂ h₁⟩

theorem Std.Antisymm.swap (r : α → α → Prop) [Std.Antisymm r] : Std.Antisymm (swap r) :=
  ⟨fun _ _ h₁ h₂ => _root_.antisymm h₂ h₁⟩

theorem Std.Asymm.swap (r : α → α → Prop) [Std.Asymm r] : Std.Asymm (swap r) :=
  ⟨fun _ _ h₁ h₂ => asymm_of r h₂ h₁⟩

@[deprecated (since := "2026-01-05")] alias IsAsymm.swap := Std.Asymm.swap

theorem Std.Total.swap (r : α → α → Prop) [Std.Total r] : Std.Total (swap r) :=
  ⟨fun a b => (total_of r a b).symm⟩

theorem Std.Trichotomous.swap (r : α → α → Prop) [Std.Trichotomous r] : Std.Trichotomous (swap r) :=
  ⟨fun a b hab hba ↦ trichotomous a b hba hab⟩

@[deprecated (since := "2026-01-24")] alias IsTrichotomous.swap := Std.Trichotomous.swap

theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  { Std.Refl.swap r, IsTrans.swap r with }

theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { Std.Irrefl.swap r, IsTrans.swap r with }

theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { IsPreorder.swap r, Std.Antisymm.swap r with }

theorem eq_empty_relation (r : α → α → Prop) [Std.Irrefl r] [Subsingleton α] : r = emptyRelation :=
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
  { Std.Trichotomous.swap r, IsStrictOrder.swap r with }

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

theorem isStrictWeakOrder_of_isOrderConnected [Std.Asymm r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @Std.Asymm.irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

-- see Note [lower instance priority]
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨fun _ _ _ h ↦ (trichotomous _ _).imp_right
    fun o ↦ o.elim (fun e ↦ e ▸ h) fun h' ↦ _root_.trans h' h⟩

/-! ### Inverse Image -/

theorem InvImage.trichotomous [Std.Trichotomous r] {f : β → α} (h : Function.Injective f) :
    Std.Trichotomous (InvImage r f) :=
  ⟨fun {a b} hab hba ↦ h <| Std.Trichotomous.trichotomous (f a) (f b) hab hba⟩

@[deprecated (since := "2026-01-24")] alias InvImage.isTrichotomous := InvImage.trichotomous

instance InvImage.asymm [Std.Asymm r] (f : β → α) : Std.Asymm (InvImage r f) where
  asymm a b h h2 := Std.Asymm.asymm (f a) (f b) h h2

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
theorem induction {motive : α → Prop} (a : α) (ind : ∀ x, (∀ y, r y x → motive y) → motive x) :
    motive a :=
  wf.induction _ ind

/-- All values are accessible under the well-founded relation. -/
theorem apply : ∀ a, Acc r a :=
  wf.apply

/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `IsWellFounded.fix_eq`. -/
def fix {motive : α → Sort*} : (ind : ∀ x : α, (∀ y : α, r y x → motive y) → motive x) →
    ∀ x : α, motive x :=
  wf.fix

/-- The value from `IsWellFounded.fix` is built from the previous ones as specified. -/
theorem fix_eq {motive : α → Sort*} (ind : ∀ x : α, (∀ y : α, r y x → motive y) → motive x) :
    ∀ x, fix r ind x = ind x fun y _ => fix r ind y :=
  wf.fix_eq ind

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
@[instance_reducible]
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
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : Std.Asymm r :=
  ⟨IsWellFounded.wf.asymmetric⟩

instance (r : α → α → Prop) [i : IsWellFounded α r] : IsWellFounded α (Relation.TransGen r) :=
  ⟨i.wf.transGen⟩

/-- A class for a well-founded relation `<`. -/
@[to_dual /-- A class for a well-founded relation `>`. -/]
abbrev WellFoundedLT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· < ·)

@[to_dual wellFounded_gt]
lemma wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α (· < ·) := IsWellFounded.wf

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) (α : Type*) [LT α] [h : WellFoundedLT α] : WellFoundedGT αᵒᵈ :=
  h

@[to_dual]
theorem wellFoundedGT_dual_iff (α : Type*) [LT α] : WellFoundedGT αᵒᵈ ↔ WellFoundedLT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
class IsWellOrder (α : Type u) (r : α → α → Prop) : Prop
    extends IsWellFounded α r, Std.Trichotomous r

instance (r) [IsWellOrder α r] : IsTrans α r where
  trans a b c hab hbc := by
    rcases trichotomous_of r a c with (hac | rfl | hca)
    · exact hac
    · exact asymm_of r hab hbc |>.elim
    · exact IsWellFounded.wf.asymmetric₃ a b c hab hbc hca |>.elim

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r where

namespace WellFoundedLT

variable [LT α] [WellFoundedLT α]

/-- Inducts on a well-founded `<` relation. -/
@[to_dual /-- Inducts on a well-founded `>` relation. -/]
theorem induction {motive : α → Prop} (a : α)
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) : motive a :=
  IsWellFounded.induction _ _ ind

/-- All values are accessible under the well-founded `<`. -/
@[to_dual /-- All values are accessible under the well-founded `>`. -/]
theorem apply : ∀ a : α, Acc (· < ·) a :=
  IsWellFounded.apply _

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLT.fix_eq`. -/
@[to_dual /-- Creates data, given a way to generate a value from all that compare as greater.
See also `WellFoundedGT.fix_eq`. -/]
def fix {motive : α → Sort*} : (ind : ∀ x : α, (∀ y : α, y < x → motive y) → motive x) →
    ∀ x : α, motive x :=
  IsWellFounded.fix (· < ·)

/-- The value from `WellFoundedLT.fix` is built from the previous ones as specified. -/
@[to_dual /-- The value from `WellFoundedGT.fix` is built from the successive ones as specified. -/]
theorem fix_eq {motive : α → Sort*} (ind : ∀ x : α, (∀ y : α, y < x → motive y) → motive x) :
    ∀ x, fix ind x = ind x fun y _ => fix ind y :=
  IsWellFounded.fix_eq _ ind

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLT` instance. -/
@[to_dual (attr := implicit_reducible)
  /-- Derive a `WellFoundedRelation` instance from a `WellFoundedGT` instance. -/]
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLT

open Classical in
/-- Construct a decidable linear order from a well-founded linear order. -/
@[implicit_reducible]
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrder α :=
  linearOrderOfSTO r

/-- Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance. -/
@[instance_reducible]
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `Std.Irrefl r`.
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α → α → Prop) [Std.Irrefl r] :
    IsWellOrder α r where
  wf := .intro fun a ↦ ⟨_, fun y h ↦ not_rel_of_subsingleton r y a h |>.elim⟩
  trichotomous a b _ _ := Subsingleton.elim a b

instance [Subsingleton α] : IsWellOrder α emptyRelation :=
  Subsingleton.isWellOrder _

instance (priority := 100) [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  wf := wellFounded_of_isEmpty r
  trichotomous := isEmptyElim

instance Prod.Lex.instIsWellFounded [IsWellFounded α r] [IsWellFounded β s] :
    IsWellFounded (α × β) (Prod.Lex r s) :=
  ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩

instance [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab hba ↦ by
    obtain rfl := Std.Trichotomous.trichotomous a₁ b₁
      (mt (Prod.Lex.left a₂ b₂) hab) (mt (Prod.Lex.left b₂ a₂) hba)
    obtain rfl := Std.Trichotomous.trichotomous a₂ b₂
      (mt (Prod.Lex.right a₁) hab) (mt (Prod.Lex.right a₁) hba)
    rfl

instance (r : α → α → Prop) [IsWellFounded α r] (f : β → α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩

instance (f : α → ℕ) : IsWellFounded _ (InvImage (· < ·) f) :=
  ⟨(measure f).wf⟩

theorem Subrelation.isWellFounded (r : α → α → Prop) [IsWellFounded α r] {s : α → α → Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩

@[to_dual]
instance Prod.wellFoundedLT [Preorder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β] :
    WellFoundedLT (α × β) where
  wf := by
    suffices h : ∀ a, ∀ a' ≤ a, ∀ b, Acc (· < ·) (a', b) from ⟨fun x => h x.1 x.1 le_rfl x.2⟩
    intro a a' ha b
    induction a using WellFoundedLT.induction generalizing a' b with | ind a iha
    induction b using WellFoundedLT.induction generalizing a' with | ind b ihb
    refine Acc.intro (a', b) fun x hx => ?_
    obtain ⟨ha', hb⟩ | ⟨ha', hb⟩ := Prod.lt_iff.1 hx
    · exact iha x.1 (ha'.trans_le ha) x.1 le_rfl x.2
    · exact ihb x.2 hb x.1 (ha'.trans ha)

@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedLT' := Prod.wellFoundedLT
@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedGT' := Prod.wellFoundedGT

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

instance instRefl [Std.Refl r] {f : β → α} : Std.Refl (f ⁻¹'o r) :=
  ⟨fun _ => refl_of r _⟩

instance instIrrefl [Std.Irrefl r] {f : β → α} : Std.Irrefl (f ⁻¹'o r) :=
  ⟨fun _ => irrefl_of r _⟩

instance instIsSymm [Std.Symm r] {f : β → α} : Std.Symm (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ symm_of r⟩

instance instAsymm [Std.Asymm r] {f : β → α} : Std.Asymm (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ asymm_of r⟩

instance instIsTrans [IsTrans α r] {f : β → α} : IsTrans β (f ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

instance instIsPreorder [IsPreorder α r] {f : β → α} : IsPreorder β (f ⁻¹'o r) where

instance instIsStrictOrder [IsStrictOrder α r] {f : β → α} : IsStrictOrder β (f ⁻¹'o r) where

instance instIsStrictWeakOrder [IsStrictWeakOrder α r] {f : β → α} :
    IsStrictWeakOrder β (f ⁻¹'o r) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

instance instIsEquiv [IsEquiv α r] {f : β → α} : IsEquiv β (f ⁻¹'o r) where

instance instTotal [Std.Total r] {f : β → α} : Std.Total (f ⁻¹'o r) :=
  ⟨fun _ _ => total_of r _ _⟩

theorem antisymm [Std.Antisymm r] {f : β → α} (hf : f.Injective) : Std.Antisymm (f ⁻¹'o r) :=
  ⟨fun _ _ h₁ h₂ ↦ hf <| antisymm_of r h₁ h₂⟩

@[deprecated (since := "2026-01-06")] alias isAntisymm := antisymm

end Order.Preimage

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `lt_iff_le_not_ge`. This is mostly meant to provide dot
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

instance {s : α → α → Prop} [IsNonstrictStrictOrder α r s] : Std.Irrefl s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section Subset

alias subset_of_eq_of_subset := le_of_eq_of_le
alias subset_of_subset_of_eq := le_of_le_of_eq
alias subset_refl := le_refl
alias subset_rfl := le_rfl
alias subset_of_eq := le_of_eq
alias superset_of_eq := ge_of_eq
alias ne_of_not_subset := ne_of_not_le
alias ne_of_not_superset := ne_of_not_ge
alias subset_trans := le_trans
alias subset_antisymm := le_antisymm
alias superset_antisymm := ge_antisymm

alias Eq.trans_subset := subset_of_eq_of_subset

alias HasSubset.subset.trans_eq := subset_of_subset_of_eq

alias Eq.subset := subset_of_eq

@[deprecated (since := "2026-01-24")] alias Eq.subset' := Eq.subset

alias Eq.superset := superset_of_eq

alias HasSubset.Subset.trans := subset_trans

alias HasSubset.Subset.antisymm := subset_antisymm

alias HasSubset.Subset.antisymm' := superset_antisymm

alias subset_antisymm_iff := le_antisymm_iff
alias superset_antisymm_iff := ge_antisymm_iff

end Subset

section SSubset

alias ssubset_of_eq_of_ssubset := lt_of_eq_of_lt
alias ssubset_of_ssubset_of_eq := lt_of_lt_of_eq
alias ssubset_irrefl := lt_irrefl
alias ne_of_ssubset := ne_of_lt
alias ne_of_ssuperset := ne_of_gt
alias ssubset_trans := lt_trans
alias ssubset_asymm := lt_asymm

alias Eq.trans_ssubset := ssubset_of_eq_of_ssubset

end SSubset

section SubsetSSubset

alias ssubset_iff_subset_not_subset := lt_iff_le_not_ge
alias subset_of_ssubset := le_of_lt
alias not_subset_of_ssubset := not_le_of_gt
alias not_ssubset_of_subset := not_lt_of_ge
alias ssubset_of_subset_not_subset := lt_of_le_not_ge

alias LT.lt.subset := subset_of_ssubset

alias LT.lt.not_subset := not_subset_of_ssubset

alias LE.le.not_ssubset := not_ssubset_of_subset

alias LE.le.ssubset_of_not_subset := ssubset_of_subset_not_subset

@[deprecated (since := "2026-03-17")]
alias HasSSubset.SSubset.subset := LT.lt.subset
@[deprecated (since := "2026-03-17")]
alias HasSSubset.SSubset.not_subset := LT.lt.not_subset
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.not_ssubset := LE.le.not_ssubset
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.ssubset_of_not_subset := LE.le.ssubset_of_not_subset



alias ssubset_of_subset_of_ssubset := lt_of_le_of_lt

alias ssubset_of_ssubset_of_subset := lt_of_lt_of_le

alias ssubset_of_subset_of_ne := lt_of_le_of_ne

theorem ssubset_of_ne_of_subset [PartialOrder α] {a b : α} : a ≠ b → a ≤ b → a < b :=
  flip ssubset_of_subset_of_ne

alias eq_or_ssubset_of_subset := eq_or_lt_of_le

alias ssubset_or_eq_of_subset := lt_or_eq_of_le

alias eq_of_subset_of_not_ssubset := eq_of_le_of_not_lt

alias eq_of_superset_of_not_ssuperset := eq_of_le_of_not_lt'

alias LE.le.trans_ssubset := ssubset_of_subset_of_ssubset

alias LT.lt.trans_subset := ssubset_of_ssubset_of_subset

alias LE.le.ssubset_of_ne := ssubset_of_subset_of_ne

alias Ne.ssubset_of_subset := ssubset_of_ne_of_subset

alias LE.le.eq_or_ssubset := eq_or_ssubset_of_subset

alias LE.le.ssubset_or_eq := ssubset_or_eq_of_subset

alias LE.le.eq_of_not_ssubset := eq_of_subset_of_not_ssubset
alias LE.le.eq_of_not_ssuperset := eq_of_superset_of_not_ssuperset

@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.trans_ssubset := LE.le.trans_ssubset
@[deprecated (since := "2026-03-17")]
alias HasSSubset.SSubset.trans_subset := LT.lt.trans_subset
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.ssubset_of_ne := LE.le.ssubset_of_ne
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.eq_or_ssubset := LE.le.eq_or_ssubset
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.ssubset_or_eq := LE.le.ssubset_or_eq
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.eq_of_not_ssubset := LE.le.eq_of_not_ssubset
@[deprecated (since := "2026-03-17")]
alias HasSubset.Subset.eq_of_not_ssuperset := LE.le.eq_of_not_ssuperset

alias ssubset_iff_subset_ne := lt_iff_le_and_ne

alias subset_iff_ssubset_or_eq := le_iff_lt_or_eq

end SubsetSSubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


@[to_dual instReflGe]
instance instReflLe [Preorder α] : @Std.Refl α (· ≤ ·) :=
  ⟨le_refl⟩

/-- A version of `Std.le_refl` that works with `Std.Refl (· ≥ ·)`.
This is needed for `to_dual` translations because `Std.le_refl` requires `Std.Refl (· ≤ ·)`,
but after translation `instReflLe` becomes `instReflGe : Std.Refl (· ≥ ·)`. -/
theorem Std.ge_refl {α : Type*} [LE α] [inst : @Std.Refl α (· ≥ ·)] (a : α) : a ≤ a :=
  @Std.Refl.refl α (· ≥ ·) inst a

set_option linter.existingAttributeWarning false in
attribute [to_dual existing Std.ge_refl] Std.le_refl

@[to_dual instIsTransGe]
instance [Preorder α] : IsTrans α (· ≤ ·) :=
  ⟨@le_trans _ _⟩

@[to_dual instIsPreorderGe]
instance [Preorder α] : IsPreorder α (· ≤ ·) where

@[to_dual instIrreflGt]
instance instIrreflLt [Preorder α] : @Std.Irrefl α (· < ·) :=
  ⟨lt_irrefl⟩

@[to_dual instIsTransGt]
instance [Preorder α] : IsTrans α (· < ·) :=
  ⟨@lt_trans _ _⟩

@[to_dual instAsymmGt]
instance instAsymmLt [Preorder α] : Std.Asymm (α := α) (· < ·) :=
  ⟨@lt_asymm _ _⟩

@[to_dual instAntisymmGt]
instance instAntisymmLt [Preorder α] : @Std.Antisymm α (· < ·) :=
  Std.Asymm.antisymm _

@[to_dual instIsStrictOrderGt]
instance [Preorder α] : IsStrictOrder α (· < ·) where

@[to_dual instIsNonstrictStrictOrderGeGt]
instance [Preorder α] : IsNonstrictStrictOrder α (· ≤ ·) (· < ·) :=
  ⟨@lt_iff_le_not_ge _ _⟩

@[to_dual instAntisymmGe]
instance instAntisymmLe [PartialOrder α] : @Std.Antisymm α (· ≤ ·) :=
  ⟨@le_antisymm _ _⟩

@[to_dual instIsPartialOrderGe]
instance [PartialOrder α] : IsPartialOrder α (· ≤ ·) where

@[to_dual total']
instance LE.total [LinearOrder α] : @Std.Total α (· ≤ ·) :=
  ⟨le_total⟩

@[to_dual instIsLinearOrderGe]
instance [LinearOrder α] : IsLinearOrder α (· ≤ ·) where

@[to_dual instTrichotomousGt]
instance instTrichotomousLt [LinearOrder α] : @Std.Trichotomous α (· < ·) :=
  ⟨by grind⟩

@[to_dual instTrichotomousGe]
instance instTrichotomousLe [LinearOrder α] : @Std.Trichotomous α (· ≤ ·) :=
  inferInstance

@[to_dual instIsStrictTotalOrderGt]
instance [LinearOrder α] : IsStrictTotalOrder α (· < ·) where

@[to_dual isTrans_ge]
theorem isTrans_le [Preorder α] : IsTrans α LE.le :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_ge := isTrans_ge
@[to_dual existing transitive_ge, deprecated (since := "2026-02-21")]
alias transitive_le := isTrans_le

@[to_dual isTrans_gt]
theorem isTrans_lt [Preorder α] : IsTrans α LT.lt :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_gt := isTrans_gt
@[to_dual existing transitive_gt, deprecated (since := "2026-02-21")]
alias transitive_lt := isTrans_lt

@[to_dual total_ge]
instance OrderDual.total_le [LE α] [h : @Std.Total α (· ≤ ·)] : @Std.Total αᵒᵈ (· ≤ ·) :=
  @Std.Total.swap α _ h

instance : WellFoundedLT ℕ :=
  ⟨Nat.lt_wfRel.wf⟩

@[to_dual isWellOrder_gt]
instance (priority := 100) isWellOrder_lt [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder α (· < ·) where
