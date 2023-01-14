/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.lists
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can be thought of (but aren't implemented) as a list of ZFA lists (not
  necessarily proper).

For example, `lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-steps definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `lists' α ff`: Atoms as ZFA prelists. Basically a copy of `α`.
* `lists' α tt`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist (`lists'.nil`)
  and from appending a ZFA prelist to a proper ZFA prelist (`lists'.cons a l`).
* `lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.

## TODO

The next step is to define ZFA sets as lists quotiented by `lists.equiv`.
(-/


variable {α : Type _}

/-- Prelists, helper type to define `lists`. `lists' α ff` are the "atoms", a copy of `α`.
`lists' α tt` are the "proper" ZFA prelists, inductively defined from the empty ZFA prelist and from
appending a ZFA prelist to a proper ZFA prelist. It is made so that you can't append anything to an
atom while having only one appending function for appending both atoms and proper ZFC prelists to a
proper ZFA prelist. -/
inductive Lists'.{u} (α : Type u) : Bool → Type u
  | atom : α → Lists' false
  | nil : Lists' true
  | cons' {b} : Lists' b → Lists' true → Lists' true
  deriving DecidableEq
#align lists' Lists'

/-- Hereditarily finite list, aka ZFA list. A ZFA list is either an "atom" (`b = ff`), corresponding
to an element of `α`, or a "proper" ZFA list, inductively defined from the empty ZFA list and from
appending a ZFA list to a proper ZFA list. -/
def Lists (α : Type _) :=
  Σb, Lists' α b
#align lists Lists

namespace Lists'

instance [Inhabited α] : ∀ b, Inhabited (Lists' α b)
  | tt => ⟨nil⟩
  | ff => ⟨atom default⟩

/-- Appending a ZFA list to a proper ZFA prelist. -/
def cons : Lists α → Lists' α true → Lists' α true
  | ⟨b, a⟩, l => cons' a l
#align lists'.cons Lists'.cons

/-- Converts a ZFA prelist to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom a => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList
#align lists'.to_list Lists'.toList

@[simp]
theorem to_list_cons (a : Lists α) (l) : toList (cons a l) = a :: l.toList := by
  cases a <;> simp [cons]
#align lists'.to_list_cons Lists'.to_list_cons

/-- Converts a `list` of ZFA lists to a proper ZFA prelist. -/
@[simp]
def ofList : List (Lists α) → Lists' α true
  | [] => nil
  | a :: l => cons a (of_list l)
#align lists'.of_list Lists'.ofList

@[simp]
theorem to_of_list (l : List (Lists α)) : toList (ofList l) = l := by induction l <;> simp [*]
#align lists'.to_of_list Lists'.to_of_list

@[simp]
theorem of_to_list : ∀ l : Lists' α true, ofList (toList l) = l :=
  suffices
    ∀ (b) (h : tt = b) (l : Lists' α b),
      let l' : Lists' α true := by rw [h] <;> exact l
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
  induction l; · cases h; · exact rfl
  case cons' b a l IH₁ IH₂ =>
    intro ; change l' with cons' a l
    simpa [cons] using IH₂ rfl
#align lists'.of_to_list Lists'.of_to_list

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    |
    antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩
  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    |
    cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' → Lists'.Subset (Lists'.cons a l) l'
end
#align lists.equiv Lists.Equiv
#align lists'.subset Lists'.Subset

-- mathport name: «expr ~ »
local infixl:50 " ~ " => Lists.Equiv

/-- Equivalence of ZFA lists. Defined inductively. -/
add_decl_doc Lists.Equiv

/-- Subset relation for ZFA lists. Defined inductively. -/
add_decl_doc Lists'.Subset

namespace Lists'

instance : HasSubset (Lists' α true) :=
  ⟨Lists'.Subset⟩

/-- ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
equivalent as a ZFA list to this ZFA list. -/
instance {b} : Membership (Lists α) (Lists' α b) :=
  ⟨fun a l => ∃ a' ∈ l.toList, a ~ a'⟩

theorem mem_def {b a} {l : Lists' α b} : a ∈ l ↔ ∃ a' ∈ l.toList, a ~ a' :=
  Iff.rfl
#align lists'.mem_def Lists'.mem_def

@[simp]
theorem mem_cons {a y l} : a ∈ @cons α y l ↔ a ~ y ∨ a ∈ l := by
  simp [mem_def, or_and_right, exists_or]
#align lists'.mem_cons Lists'.mem_cons

theorem cons_subset {a} {l₁ l₂ : Lists' α true} : Lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ :=
  by
  refine' ⟨fun h => _, fun ⟨⟨a', m, e⟩, s⟩ => subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁' at h
  cases' h with l a' a'' l l' e m s;
  · cases a
    cases h'
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩
#align lists'.cons_subset Lists'.cons_subset

theorem of_list_subset {l₁ l₂ : List (Lists α)} (h : l₁ ⊆ l₂) :
    Lists'.ofList l₁ ⊆ Lists'.ofList l₂ := by
  induction l₁; · exact subset.nil
  refine' subset.cons (Lists.Equiv.refl _) _ (l₁_ih (List.subset_of_cons_subset h))
  simp at h; simp [h]
#align lists'.of_list_subset Lists'.of_list_subset

@[refl]
theorem Subset.refl {l : Lists' α true} : l ⊆ l := by
  rw [← Lists'.of_to_list l] <;> exact of_list_subset (List.Subset.refl _)
#align lists'.subset.refl Lists'.Subset.refl

theorem subset_nil {l : Lists' α true} : l ⊆ Lists'.nil → l = Lists'.nil :=
  by
  rw [← of_to_list l]
  induction to_list l <;> intro h; · rfl
  rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩
#align lists'.subset_nil Lists'.subset_nil

theorem mem_of_subset' {a} {l₁ l₂ : Lists' α true} (s : l₁ ⊆ l₂) (h : a ∈ l₁.toList) : a ∈ l₂ :=
  by
  induction' s with _ a a' l l' e m s IH; · cases h
  simp at h; rcases h with (rfl | h)
  exacts[⟨_, m, e⟩, IH h]
#align lists'.mem_of_subset' Lists'.mem_of_subset'

theorem subset_def {l₁ l₂ : Lists' α true} : l₁ ⊆ l₂ ↔ ∀ a ∈ l₁.toList, a ∈ l₂ :=
  ⟨fun H a => mem_of_subset' H, fun H =>
    by
    rw [← of_to_list l₁]
    revert H; induction to_list l₁ <;> intro
    · exact subset.nil
    · simp at H
      exact cons_subset.2 ⟨H.1, ih H.2⟩⟩
#align lists'.subset_def Lists'.subset_def

end Lists'

namespace Lists

/-- Sends `a : α` to the corresponding atom in `lists α`. -/
@[match_pattern]
def atom (a : α) : Lists α :=
  ⟨_, Lists'.atom a⟩
#align lists.atom Lists.atom

/-- Converts a proper ZFA prelist to a ZFA list. -/
@[match_pattern]
def of' (l : Lists' α true) : Lists α :=
  ⟨_, l⟩
#align lists.of' Lists.of'

/-- Converts a ZFA list to a `list` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : Lists α → List (Lists α)
  | ⟨b, l⟩ => l.toList
#align lists.to_list Lists.toList

/-- Predicate stating that a ZFA list is proper. -/
def IsList (l : Lists α) : Prop :=
  l.1
#align lists.is_list Lists.IsList

/-- Converts a `list` of ZFA lists to a ZFA list. -/
def ofList (l : List (Lists α)) : Lists α :=
  of' (Lists'.ofList l)
#align lists.of_list Lists.ofList

theorem is_list_to_list (l : List (Lists α)) : IsList (ofList l) :=
  Eq.refl _
#align lists.is_list_to_list Lists.is_list_to_list

theorem to_of_list (l : List (Lists α)) : toList (ofList l) = l := by simp [of_list, of']
#align lists.to_of_list Lists.to_of_list

theorem of_to_list : ∀ {l : Lists α}, IsList l → ofList (toList l) = l
  | ⟨tt, l⟩, _ => by simp [of_list, of']
#align lists.of_to_list Lists.of_to_list

instance : Inhabited (Lists α) :=
  ⟨of' Lists'.nil⟩

instance [DecidableEq α] : DecidableEq (Lists α) := by unfold Lists <;> infer_instance

instance [SizeOf α] : SizeOf (Lists α) := by unfold Lists <;> infer_instance

/-- A recursion principle for pairs of ZFA lists and proper ZFA prelists. -/
def inductionMut (C : Lists α → Sort _) (D : Lists' α true → Sort _) (C0 : ∀ a, C (atom a))
    (C1 : ∀ l, D l → C (of' l)) (D0 : D Lists'.nil) (D1 : ∀ a l, C a → D l → D (Lists'.cons a l)) :
    PProd (∀ l, C l) (∀ l, D l) :=
  by
  suffices
    ∀ {b} (l : Lists' α b),
      PProd (C ⟨_, l⟩)
        (match b, l with
        | tt, l => D l
        | ff, l => PUnit)
    by exact ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intros
  induction' l with a b a l IH₁ IH₂
  · exact ⟨C0 _, ⟨⟩⟩
  · exact ⟨C1 _ D0, D0⟩
  · suffices
    · exact ⟨C1 _ this, this⟩
    exact D1 ⟨_, _⟩ _ IH₁.1 IH₂.2
#align lists.induction_mut Lists.inductionMut

/-- Membership of ZFA list. A ZFA list belongs to a proper ZFA list if it belongs to the latter as a
proper ZFA prelist. An atom has no members. -/
def Mem (a : Lists α) : Lists α → Prop
  | ⟨ff, l⟩ => False
  | ⟨tt, l⟩ => a ∈ l
#align lists.mem Lists.Mem

instance : Membership (Lists α) (Lists α) :=
  ⟨Mem⟩

theorem is_list_of_mem {a : Lists α} : ∀ {l : Lists α}, a ∈ l → IsList l
  | ⟨_, Lists'.nil⟩, _ => rfl
  | ⟨_, Lists'.cons' _ _⟩, _ => rfl
#align lists.is_list_of_mem Lists.is_list_of_mem

theorem Equiv.antisymm_iff {l₁ l₂ : Lists' α true} : of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ :=
  by
  refine' ⟨fun h => _, fun ⟨h₁, h₂⟩ => equiv.antisymm h₁ h₂⟩
  cases' h with _ _ _ h₁ h₂
  · simp [Lists'.Subset.refl]; · exact ⟨h₁, h₂⟩
#align lists.equiv.antisymm_iff Lists.Equiv.antisymm_iff

attribute [refl] Equiv.refl

theorem equiv_atom {a} {l : Lists α} : atom a ~ l ↔ atom a = l :=
  ⟨fun h => by cases h <;> rfl, fun h => h ▸ Equiv.refl _⟩
#align lists.equiv_atom Lists.equiv_atom

theorem Equiv.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  cases' h with _ _ _ h₁ h₂ <;> [rfl, exact equiv.antisymm h₂ h₁]
#align lists.equiv.symm Lists.Equiv.symm

theorem Equiv.trans : ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
  by
  let trans := fun l₁ : Lists α => ∀ ⦃l₂ l₃⦄, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  suffices PProd (∀ l₁, trans l₁) (∀ (l : Lists' α tt), ∀ l' ∈ l.toList, trans l') by exact this.1
  apply induction_mut
  · intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  · intro l₁ IH l₂ l₃ h₁ h₂
    cases' h₁ with _ _ l₂
    · exact h₂
    cases' h₂ with _ _ l₃
    · exact h₁
    cases' equiv.antisymm_iff.1 h₁ with hl₁ hr₁
    cases' equiv.antisymm_iff.1 h₂ with hl₂ hr₂
    apply equiv.antisymm_iff.2 <;> constructor <;> apply Lists'.subset_def.2
    · intro a₁ m₁
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
    · intro a₃ m₃
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
  · rintro _ ⟨⟩
  · intro a l IH₁ IH₂
    simpa [IH₁] using IH₂
#align lists.equiv.trans Lists.Equiv.trans

instance : Setoid (Lists α) :=
  ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

section Decidable

@[simp]
def Equiv.decidableMeas :
    (PSum (Σ'l₁ : Lists α, Lists α) <|
        PSum (Σ'l₁ : Lists' α true, Lists' α true) (Σ'a : Lists α, Lists' α true)) →
      ℕ
  | PSum.inl ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
  | PSum.inr <| PSum.inl ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
  | PSum.inr <| PSum.inr ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
#align lists.equiv.decidable_meas Lists.Equiv.decidableMeas

open WellFoundedTactics

theorem sizeof_pos {b} (l : Lists' α b) : 0 < SizeOf.sizeOf l := by
  cases l <;>
    run_tac
      andthen unfold_sizeof trivial_nat_lt
#align lists.sizeof_pos Lists.sizeof_pos

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic well_founded_tactics.unfold_sizeof -/
theorem lt_sizeof_cons' {b} (a : Lists' α b) (l) :
    SizeOf.sizeOf (⟨b, a⟩ : Lists α) < SizeOf.sizeOf (Lists'.cons' a l) :=
  by
  run_tac
    unfold_sizeof
  apply sizeof_pos
#align lists.lt_sizeof_cons' Lists.lt_sizeof_cons'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic well_founded_tactics.default_dec_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic well_founded_tactics.default_dec_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic well_founded_tactics.default_dec_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic well_founded_tactics.default_dec_tac -/
mutual
  @[instance]
  def Equiv.decidable [DecidableEq α] : ∀ l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
    | ⟨ff, l₁⟩, ⟨ff, l₂⟩ =>
      decidable_of_iff' (l₁ = l₂) <| by cases l₁ <;> refine' equiv_atom.trans (by simp [atom])
    | ⟨ff, l₁⟩, ⟨tt, l₂⟩ => is_false <| by rintro ⟨⟩
    | ⟨tt, l₁⟩, ⟨ff, l₂⟩ => is_false <| by rintro ⟨⟩
    | ⟨tt, l₁⟩, ⟨tt, l₂⟩ =>
      by
      haveI :=
        have :
          SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨tt, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨tt, l₂⟩ : Lists α) :=
          by
          run_tac
            default_dec_tac
        subset.decidable l₁ l₂
      haveI :=
        have :
          SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨tt, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨tt, l₂⟩ : Lists α) :=
          by
          run_tac
            default_dec_tac
        subset.decidable l₂ l₁
      exact decidable_of_iff' _ equiv.antisymm_iff
  @[instance]
  def Subset.decidable [DecidableEq α] : ∀ l₁ l₂ : Lists' α true, Decidable (l₁ ⊆ l₂)
    | Lists'.nil, l₂ => isTrue Subset.nil
    | @Lists'.cons' _ b a l₁, l₂ =>
      by
      haveI :=
        have :
          SizeOf.sizeOf (⟨b, a⟩ : Lists α) + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ :=
          add_lt_add_right (lt_sizeof_cons' _ _) _
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have :
          SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ :=
          by
          run_tac
            default_dec_tac
        subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  @[instance]
  def Mem.decidable [DecidableEq α] : ∀ (a : Lists α) (l : Lists' α true), Decidable (a ∈ l)
    | a, Lists'.nil => is_false <| by rintro ⟨_, ⟨⟩, _⟩
    | a, Lists'.cons' b l₂ =>
      by
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf (⟨_, b⟩ : Lists α) <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) :=
          add_lt_add_left (lt_sizeof_cons' _ _) _
        equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) :=
          by
          run_tac
            default_dec_tac
        mem.decidable a l₂
      refine' decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a ∈ l₂) _
      rw [← Lists'.mem_cons]; rfl
end termination_by' ⟨_, measure_wf equiv.decidable_meas⟩
#align lists.equiv.decidable Lists.Equiv.decidable
#align lists.subset.decidable Lists.Subset.decidable
#align lists.mem.decidable Lists.Mem.decidable

end Decidable

end Lists

namespace Lists'

theorem mem_equiv_left {l : Lists' α true} : ∀ {a a'}, a ~ a' → (a ∈ l ↔ a' ∈ l) :=
  suffices ∀ {a a'}, a ~ a' → a ∈ l → a' ∈ l from fun a a' e => ⟨this e, this e.symm⟩
  fun a₁ a₂ e₁ ⟨a₃, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩
#align lists'.mem_equiv_left Lists'.mem_equiv_left

theorem mem_of_subset {a} {l₁ l₂ : Lists' α true} (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂
  | ⟨a', m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)
#align lists'.mem_of_subset Lists'.mem_of_subset

theorem Subset.trans {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  subset_def.2 fun a₁ m₁ => mem_of_subset h₂ <| mem_of_subset' h₁ m₁
#align lists'.subset.trans Lists'.Subset.trans

end Lists'

def Finsets (α : Type _) :=
  Quotient (@Lists.setoid α)
#align finsets Finsets

namespace Finsets

instance : EmptyCollection (Finsets α) :=
  ⟨⟦Lists.of' Lists'.nil⟧⟩

instance : Inhabited (Finsets α) :=
  ⟨∅⟩

instance [DecidableEq α] : DecidableEq (Finsets α) := by unfold Finsets <;> infer_instance

end Finsets

