/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Sigma.Basic
import Mathlib.Algebra.Order.Ring.Nat

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can be thought of (but are not implemented) as a list of ZFA lists (not
  necessarily proper).

For example, `Lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-step definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `Lists' α false`: Atoms as ZFA prelists. Basically a copy of `α`.
* `Lists' α true`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist
  (`Lists'.nil`) and from appending a ZFA prelist to a proper ZFA prelist (`Lists'.cons a l`).
* `Lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.
* `Finsets α`: ZFA sets. Defined as `Lists` quotiented by `Lists.Equiv`, the extensional
  equivalence.
-/


variable {α : Type*}

/-- Prelists, helper type to define `Lists`. `Lists' α false` are the "atoms", a copy of `α`.
`Lists' α true` are the "proper" ZFA prelists, inductively defined from the empty ZFA prelist and
from appending a ZFA prelist to a proper ZFA prelist. It is made so that you can't append anything
to an atom while having only one appending function for appending both atoms and proper ZFA prelists
to a proper ZFA prelist. -/
inductive Lists'.{u} (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true
  deriving DecidableEq
compile_inductive% Lists'

/-- Hereditarily finite list, aka ZFA list. A ZFA list is either an "atom" (`b = false`),
corresponding to an element of `α`, or a "proper" ZFA list, inductively defined from the empty ZFA
list and from appending a ZFA list to a proper ZFA list. -/
def Lists (α : Type*) :=
  Σ b, Lists' α b

namespace Lists'

instance [Inhabited α] : ∀ b, Inhabited (Lists' α b)
  | true => ⟨nil⟩
  | false => ⟨atom default⟩

/-- Appending a ZFA list to a proper ZFA prelist. -/
def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l

/-- Converts a ZFA prelist to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList

@[simp]
theorem toList_cons (a : Lists α) (l) : toList (cons a l) = a :: l.toList := rfl

/-- Converts a `List` of ZFA lists to a proper ZFA prelist. -/
@[simp]
def ofList : List (Lists α) → Lists' α true
  | [] => nil
  | a :: l => cons a (ofList l)

@[simp]
theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by induction l <;> simp [*]

set_option linter.style.commandStart false in -- TODO decide about this!
@[simp]
theorem of_toList : ∀ l : Lists' α true, ofList (toList l) = l :=
  suffices
    ∀ (b) (h : true = b) (l : Lists' α b),
      let l' : Lists' α true := by rw [h]; exact l
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
    induction l with
    | atom => cases h
    | nil => simp
    | cons' b a _ IH => simpa [cons] using IH rfl

/-- Recursion/induction principle for `Lists'.ofList`. -/
@[elab_as_elim]
def recOfList {motive : Lists' α true → Sort*} (ofList : ∀ l, motive (ofList l)) : ∀ l, motive l :=
  fun l ↦ cast (by simp) <| ofList (l.toList)

end Lists'

mutual
  /-- Equivalence of ZFA lists. Defined inductively. -/
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩

  /-- Subset relation for ZFA lists. Defined inductively. -/
  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' → Lists'.Subset (Lists'.cons a l) l'
end

local infixl:50 " ~ " => Lists.Equiv

namespace Lists'

instance : HasSubset (Lists' α true) :=
  ⟨Lists'.Subset⟩

/-- ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
equivalent as a ZFA list to this ZFA list. -/
instance {b} : Membership (Lists α) (Lists' α b) :=
  ⟨fun l a => ∃ a' ∈ l.toList, a ~ a'⟩

theorem mem_def {b a} {l : Lists' α b} : a ∈ l ↔ ∃ a' ∈ l.toList, a ~ a' :=
  Iff.rfl

@[simp]
theorem mem_cons {a y l} : a ∈ @cons α y l ↔ a ~ y ∨ a ∈ l := by
  simp [mem_def, or_and_right, exists_or]

theorem cons_subset {a} {l₁ l₂ : Lists' α true} : Lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ := by
  refine ⟨fun h => ?_, fun ⟨⟨a', m, e⟩, s⟩ => Subset.cons e m s⟩
  generalize h' : Lists'.cons a l₁ = l₁' at h
  obtain - | @⟨a', _, _, _, e, m, s⟩ := h
  · cases a
    cases h'
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩

theorem ofList_subset {l₁ l₂ : List (Lists α)} (h : l₁ ⊆ l₂) :
    Lists'.ofList l₁ ⊆ Lists'.ofList l₂ := by
  induction l₁ with
  | nil => exact Subset.nil
  | cons _ _ l₁_ih =>
    refine Subset.cons (Lists.Equiv.refl _) ?_ (l₁_ih (List.subset_of_cons_subset h))
    simp only [List.cons_subset] at h; simp [h]

@[refl]
theorem Subset.refl {l : Lists' α true} : l ⊆ l := by
  rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)

theorem subset_nil {l : Lists' α true} : l ⊆ Lists'.nil → l = Lists'.nil := by
  rw [← of_toList l]
  induction toList l <;> intro h
  · rfl
  · rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩

theorem mem_of_subset' {a} : ∀ {l₁ l₂ : Lists' α true} (_ : l₁ ⊆ l₂) (_ : a ∈ l₁.toList), a ∈ l₂
  | nil, _, Lists'.Subset.nil, h => by cases h
  | cons' a0 l0, l₂, s, h => by
    obtain - | ⟨e, m, s⟩ := s
    simp only [toList, Sigma.eta, List.mem_cons] at h
    rcases h with (rfl | h)
    · exact ⟨_, m, e⟩
    · exact mem_of_subset' s h

theorem subset_def {l₁ l₂ : Lists' α true} : l₁ ⊆ l₂ ↔ ∀ a ∈ l₁.toList, a ∈ l₂ :=
  ⟨fun H _ => mem_of_subset' H, fun H => by
    induction l₁ using recOfList with | _ l₁
    induction l₁ with
    | nil => exact Subset.nil
    | cons h t t_ih =>
      simp only [to_ofList, ofList, toList_cons, List.mem_cons, forall_eq_or_imp] at *
      exact cons_subset.2 ⟨H.1, t_ih H.2⟩⟩

end Lists'

namespace Lists

/-- Sends `a : α` to the corresponding atom in `Lists α`. -/
@[match_pattern]
def atom (a : α) : Lists α :=
  ⟨_, Lists'.atom a⟩

/-- Converts a proper ZFA prelist to a ZFA list. -/
@[match_pattern]
def of' (l : Lists' α true) : Lists α :=
  ⟨_, l⟩

/-- Converts a ZFA list to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : Lists α → List (Lists α)
  | ⟨_, l⟩ => l.toList

/-- Predicate stating that a ZFA list is proper. -/
def IsList (l : Lists α) : Prop :=
  l.1

/-- Converts a `List` of ZFA lists to a ZFA list. -/
def ofList (l : List (Lists α)) : Lists α :=
  of' (Lists'.ofList l)

theorem isList_toList (l : List (Lists α)) : IsList (ofList l) :=
  Eq.refl _

theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by simp [ofList, of']

theorem of_toList : ∀ {l : Lists α}, IsList l → ofList (toList l) = l
  | ⟨true, l⟩, _ => by simp_all [ofList, of']

instance : Inhabited (Lists α) :=
  ⟨of' Lists'.nil⟩

instance [DecidableEq α] : DecidableEq (Lists α) := by unfold Lists; infer_instance

instance [SizeOf α] : SizeOf (Lists α) := by unfold Lists; infer_instance

set_option linter.style.commandStart false in -- TODO decide about this!
/-- A recursion principle for pairs of ZFA lists and proper ZFA prelists. -/
def inductionMut (C : Lists α → Sort*) (D : Lists' α true → Sort*)
    (C0 : ∀ a, C (atom a)) (C1 : ∀ l, D l → C (of' l))
    (D0 : D Lists'.nil) (D1 : ∀ a l, C a → D l → D (Lists'.cons a l)) :
    PProd (∀ l, C l) (∀ l, D l) := by
  suffices
    ∀ {b} (l : Lists' α b),
      PProd (C ⟨_, l⟩)
        (match b, l with
        | true, l => D l
        | false, _ => PUnit)
    by exact ⟨fun ⟨b, l⟩ => (this _).1, fun l => (this l).2⟩
  intro b l
  induction l with
  | atom => exact ⟨C0 _, ⟨⟩⟩
  | nil => exact ⟨C1 _ D0, D0⟩
  | cons' a l IH₁ IH =>
    have : D (Lists'.cons' a l) := D1 ⟨_, _⟩ _ IH₁.1 IH.2
    exact ⟨C1 _ this, this⟩

/-- Membership of ZFA list. A ZFA list belongs to a proper ZFA list if it belongs to the latter as a
proper ZFA prelist. An atom has no members. -/
def mem (a : Lists α) : Lists α → Prop
  | ⟨false, _⟩ => False
  | ⟨_, l⟩ => a ∈ l

instance : Membership (Lists α) (Lists α) where
  mem ls l := mem l ls

theorem isList_of_mem {a : Lists α} : ∀ {l : Lists α}, a ∈ l → IsList l
  | ⟨_, Lists'.nil⟩, _ => rfl
  | ⟨_, Lists'.cons' _ _⟩, _ => rfl

theorem Equiv.antisymm_iff {l₁ l₂ : Lists' α true} : of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => Equiv.antisymm h₁ h₂⟩
  obtain - | ⟨h₁, h₂⟩ := h
  · simp [Lists'.Subset.refl]
  · exact ⟨h₁, h₂⟩

attribute [refl] Equiv.refl

theorem equiv_atom {a} {l : Lists α} : atom a ~ l ↔ atom a = l :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Equiv.refl _⟩

@[symm]
theorem Equiv.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  obtain - | ⟨h₁, h₂⟩ := h <;> [rfl; exact Equiv.antisymm h₂ h₁]

theorem Equiv.trans : ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ := by
  let trans := fun l₁ : Lists α => ∀ ⦃l₂ l₃⦄, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  suffices PProd (∀ l₁, trans l₁) (∀ (l : Lists' α true), ∀ l' ∈ l.toList, trans l') by exact this.1
  apply inductionMut
  · intro a l₂ l₃ h₁ h₂
    rwa [← equiv_atom.1 h₁] at h₂
  · intro l₁ IH l₂ l₃ h₁ h₂
    obtain - | l₂ := id h₁
    · exact h₂
    obtain - | l₃ := id h₂
    · exact h₁
    obtain ⟨hl₁, hr₁⟩ := Equiv.antisymm_iff.1 h₁
    obtain ⟨hl₂, hr₂⟩ := Equiv.antisymm_iff.1 h₂
    apply Equiv.antisymm_iff.2; constructor <;> apply Lists'.subset_def.2
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
    simpa using ⟨IH₁, IH₂⟩

instance instSetoidLists : Setoid (Lists α) :=
  ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

section Decidable

theorem sizeof_pos {b} (l : Lists' α b) : 0 < SizeOf.sizeOf l := by
  cases l <;> simp only [Lists'.atom.sizeOf_spec, Lists'.nil.sizeOf_spec, Lists'.cons'.sizeOf_spec,
    true_or, add_pos_iff, zero_lt_one]

theorem lt_sizeof_cons' {b} (a : Lists' α b) (l) :
    SizeOf.sizeOf (⟨b, a⟩ : Lists α) < SizeOf.sizeOf (Lists'.cons' a l) := by
  simp only [Sigma.mk.sizeOf_spec, Lists'.cons'.sizeOf_spec, lt_add_iff_pos_right]
  apply sizeof_pos

variable [DecidableEq α]

mutual
  instance Equiv.decidable : ∀ l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
    | ⟨false, l₁⟩, ⟨false, l₂⟩ =>
      decidable_of_iff' (l₁ = l₂) <| by
        cases l₁
        apply equiv_atom.trans
        simp only [atom]
        constructor <;> (rintro ⟨rfl⟩; rfl)
    | ⟨false, l₁⟩, ⟨true, l₂⟩ => isFalse <| by rintro ⟨⟩
    | ⟨true, l₁⟩, ⟨false, l₂⟩ => isFalse <| by rintro ⟨⟩
    | ⟨true, l₁⟩, ⟨true, l₂⟩ => by
      haveI : Decidable (l₁ ⊆ l₂) :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      haveI : Decidable (l₂ ⊆ l₁) :=
        have : SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) := by
          decreasing_tactic
        Subset.decidable l₂ l₁
      exact decidable_of_iff' _ Equiv.antisymm_iff
  termination_by x y => sizeOf x + sizeOf y
  instance Subset.decidable : ∀ l₁ l₂ : Lists' α true, Decidable (l₁ ⊆ l₂)
    | Lists'.nil, _ => isTrue Lists'.Subset.nil
    | @Lists'.cons' _ b a l₁, l₂ => by
      haveI :=
        have : sizeOf (⟨b, a⟩ : Lists α) < 1 + 1 + sizeOf a + sizeOf l₁ := by simp [sizeof_pos]
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ := by
          decreasing_tactic
        Subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
  termination_by x y => sizeOf x + sizeOf y
  instance mem.decidable : ∀ (a : Lists α) (l : Lists' α true), Decidable (a ∈ l)
    | a, Lists'.nil => isFalse <| by rintro ⟨_, ⟨⟩, _⟩
    | a, Lists'.cons' b l₂ => by
      haveI :=
        have : sizeOf (⟨_, b⟩ : Lists α) < 1 + 1 + sizeOf b + sizeOf l₂ := by simp [sizeof_pos]
        Equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) := by
          decreasing_tactic
        mem.decidable a l₂
      refine decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a ∈ l₂) ?_
      rw [← Lists'.mem_cons]; rfl
  termination_by x y => sizeOf x + sizeOf y
end

/-- Copy over the decidability to the `Setoid` instance. -/
instance : DecidableRel ((· ≈ ·) : Lists α → Lists α → Prop) :=
  Lists.Equiv.decidable

-- This is an autogenerated declaration, so there's nothing we can do about it.
attribute [nolint nonClassInstance] Lists.Equiv.decidable._mutual

end Decidable

end Lists

namespace Lists'

theorem mem_equiv_left {l : Lists' α true} : ∀ {a a'}, a ~ a' → (a ∈ l ↔ a' ∈ l) :=
  suffices ∀ {a a'}, a ~ a' → a ∈ l → a' ∈ l from fun e => ⟨this e, this e.symm⟩
  fun e₁ ⟨_, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩

theorem mem_of_subset {a} {l₁ l₂ : Lists' α true} (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂
  | ⟨_, m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)

theorem Subset.trans {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  subset_def.2 fun _ m₁ => mem_of_subset h₂ <| mem_of_subset' h₁ m₁

end Lists'

/-- `Finsets` are defined via equivalence classes of `Lists` -/
def Finsets (α : Type*) :=
  Quotient (@Lists.instSetoidLists α)

namespace Finsets

instance : EmptyCollection (Finsets α) :=
  ⟨⟦Lists.of' Lists'.nil⟧⟩

instance : Inhabited (Finsets α) :=
  ⟨∅⟩

instance [DecidableEq α] : DecidableEq (Finsets α) :=
  inferInstanceAs <| DecidableEq (Quotient Lists.instSetoidLists)

end Finsets
