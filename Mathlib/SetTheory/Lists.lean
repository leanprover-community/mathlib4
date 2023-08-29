/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

#align_import set_theory.lists from "leanprover-community/mathlib"@"497d1e06409995dd8ec95301fa8d8f3480187f4c"

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can be thought of (but aren't implemented) as a list of ZFA lists (not
  necessarily proper).

For example, `Lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-steps definition of ZFA lists:
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
to an atom while having only one appending function for appending both atoms and proper ZFC prelists
to a proper ZFA prelist. -/
inductive Lists'.{u} (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true
  deriving DecidableEq
#align lists' Lists'
compile_inductive% Lists'

/-- Hereditarily finite list, aka ZFA list. A ZFA list is either an "atom" (`b = false`),
corresponding to an element of `α`, or a "proper" ZFA list, inductively defined from the empty ZFA
list and from appending a ZFA list to a proper ZFA list. -/
def Lists (α : Type*) :=
  Σb, Lists' α b
#align lists Lists

namespace Lists'

instance [Inhabited α] : ∀ b, Inhabited (Lists' α b)
  | true => ⟨nil⟩
  | false => ⟨atom default⟩

/-- Appending a ZFA list to a proper ZFA prelist. -/
def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l
#align lists'.cons Lists'.cons

/-- Converts a ZFA prelist to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : ∀ {b}, Lists' α b → List (Lists α)
  | _, atom _ => []
  | _, nil => []
  | _, cons' a l => ⟨_, a⟩ :: l.toList
#align lists'.to_list Lists'.toList

-- porting notes: removed @[simp]
-- simp can prove this: by simp only [@Lists'.toList, @Sigma.eta]
theorem toList_cons (a : Lists α) (l) : toList (cons a l) = a :: l.toList := by simp
                                                                                -- 🎉 no goals
#align lists'.to_list_cons Lists'.toList_cons

/-- Converts a `List` of ZFA lists to a proper ZFA prelist. -/
@[simp]
def ofList : List (Lists α) → Lists' α true
  | [] => nil
  | a :: l => cons a (ofList l)
#align lists'.of_list Lists'.ofList

@[simp]
theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by induction l <;> simp [*]
                                                                     -- ⊢ toList (ofList []) = []
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align lists'.to_of_list Lists'.to_ofList

@[simp]
theorem of_toList : ∀ l : Lists' α true, ofList (toList l) = l :=
  suffices
    ∀ (b) (h : true = b) (l : Lists' α b),
      let l' : Lists' α true := by rw [h]; exact l
                                   -- ⊢ Lists' α b
                                           -- 🎉 no goals
      ofList (toList l') = l'
    from this _ rfl
  fun b h l => by
    induction l with
    | atom => cases h
    -- Porting note: case nil was not covered.
    | nil => simp
    | cons' b a _ IH =>
      intro l'
      -- Porting note: Previous code was:
      -- change l' with cons' a l
      --
      -- This can be removed.
      simpa [cons] using IH rfl
#align lists'.of_to_list Lists'.of_toList

end Lists'

mutual
  inductive Lists.Equiv : Lists α → Lists α → Prop
    | refl (l) : Lists.Equiv l l
    | antisymm {l₁ l₂ : Lists' α true} :
      Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_, l₂⟩
  inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
    | nil {l} : Lists'.Subset Lists'.nil l
    | cons {a a' l l'} :
      Lists.Equiv a a' →
        a' ∈ Lists'.toList l' → Lists'.Subset l l' → Lists'.Subset (Lists'.cons a l) l'
end
#align lists.equiv Lists.Equiv
#align lists'.subset Lists'.Subset

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
  -- 🎉 no goals
#align lists'.mem_cons Lists'.mem_cons

theorem cons_subset {a} {l₁ l₂ : Lists' α true} : Lists'.cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ := by
  refine' ⟨fun h => _, fun ⟨⟨a', m, e⟩, s⟩ => Subset.cons e m s⟩
  -- ⊢ a ∈ l₂ ∧ l₁ ⊆ l₂
  generalize h' : Lists'.cons a l₁ = l₁' at h
  -- ⊢ a ∈ l₂ ∧ l₁ ⊆ l₂
  cases' h with l a' a'' l l' e m s;
  -- ⊢ a ∈ l₂ ∧ l₁ ⊆ l₂
  · cases a
    -- ⊢ { fst := fst✝, snd := snd✝ } ∈ l₂ ∧ l₁ ⊆ l₂
    cases h'
    -- 🎉 no goals
  cases a; cases a'; cases h'; exact ⟨⟨_, m, e⟩, s⟩
  -- ⊢ { fst := fst✝, snd := snd✝ } ∈ l₂ ∧ l₁ ⊆ l₂
           -- ⊢ { fst := fst✝¹, snd := snd✝¹ } ∈ l₂ ∧ l₁ ⊆ l₂
                     -- ⊢ { fst := fst✝, snd := snd✝ } ∈ l₂ ∧ l₁ ⊆ l₂
                               -- 🎉 no goals
#align lists'.cons_subset Lists'.cons_subset

theorem ofList_subset {l₁ l₂ : List (Lists α)} (h : l₁ ⊆ l₂) :
    Lists'.ofList l₁ ⊆ Lists'.ofList l₂ := by
  induction' l₁ with _ _ l₁_ih; · exact Subset.nil
  -- ⊢ ofList [] ⊆ ofList l₂
                                  -- 🎉 no goals
  refine' Subset.cons (Lists.Equiv.refl _) _ (l₁_ih (List.subset_of_cons_subset h))
  -- ⊢ head✝ ∈ toList (ofList l₂)
  simp at h; simp [h]
  -- ⊢ head✝ ∈ toList (ofList l₂)
             -- 🎉 no goals
#align lists'.of_list_subset Lists'.ofList_subset

@[refl]
theorem Subset.refl {l : Lists' α true} : l ⊆ l := by
  rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)
  -- ⊢ ofList (toList l) ⊆ ofList (toList l)
                             -- 🎉 no goals
#align lists'.subset.refl Lists'.Subset.refl

theorem subset_nil {l : Lists' α true} : l ⊆ Lists'.nil → l = Lists'.nil := by
  rw [← of_toList l]
  -- ⊢ ofList (toList l) ⊆ nil → ofList (toList l) = nil
  induction toList l <;> intro h
  -- ⊢ ofList [] ⊆ nil → ofList [] = nil
                         -- ⊢ ofList [] = nil
                         -- ⊢ ofList (head✝ :: tail✝) = nil
  · rfl
    -- 🎉 no goals
  · rcases cons_subset.1 h with ⟨⟨_, ⟨⟩, _⟩, _⟩
    -- 🎉 no goals
#align lists'.subset_nil Lists'.subset_nil

theorem mem_of_subset' {a} : ∀ {l₁ l₂ : Lists' α true} (_ : l₁ ⊆ l₂) (_ : a ∈ l₁.toList), a ∈ l₂
  | nil, _, Lists'.Subset.nil, h => by cases h
                                       -- 🎉 no goals
  | cons' a0 l0, l₂, s, h => by
    cases' s with _ _ _ _ _ e m s
    -- ⊢ a ∈ l₂
    simp only [toList, Sigma.eta, List.find?, List.mem_cons] at h
    -- ⊢ a ∈ l₂
    rcases h with (rfl | h)
    -- ⊢ a ∈ l₂
    · exact ⟨_, m, e⟩
      -- 🎉 no goals
    · exact mem_of_subset' s h
      -- 🎉 no goals
#align lists'.mem_of_subset' Lists'.mem_of_subset'

theorem subset_def {l₁ l₂ : Lists' α true} : l₁ ⊆ l₂ ↔ ∀ a ∈ l₁.toList, a ∈ l₂ :=
  ⟨fun H a => mem_of_subset' H, fun H => by
    rw [← of_toList l₁]
    -- ⊢ ofList (toList l₁) ⊆ l₂
    revert H; induction' toList l₁ with h t t_ih <;> intro H
    -- ⊢ (∀ (a : Lists α), a ∈ toList l₁ → a ∈ l₂) → ofList (toList l₁) ⊆ l₂
              -- ⊢ (∀ (a : Lists α), a ∈ [] → a ∈ l₂) → ofList [] ⊆ l₂
                                                     -- ⊢ ofList [] ⊆ l₂
                                                     -- ⊢ ofList (h :: t) ⊆ l₂
    · exact Subset.nil
      -- 🎉 no goals
    · simp only [ofList, List.find?, List.mem_cons, forall_eq_or_imp] at *
      -- ⊢ cons h (ofList t) ⊆ l₂
      exact cons_subset.2 ⟨H.1, t_ih H.2⟩⟩
      -- 🎉 no goals
#align lists'.subset_def Lists'.subset_def

end Lists'

namespace Lists

/-- Sends `a : α` to the corresponding atom in `Lists α`. -/
@[match_pattern]
def atom (a : α) : Lists α :=
  ⟨_, Lists'.atom a⟩
#align lists.atom Lists.atom

/-- Converts a proper ZFA prelist to a ZFA list. -/
@[match_pattern]
def of' (l : Lists' α true) : Lists α :=
  ⟨_, l⟩
#align lists.of' Lists.of'

/-- Converts a ZFA list to a `List` of ZFA lists. Atoms are sent to `[]`. -/
@[simp]
def toList : Lists α → List (Lists α)
  | ⟨_, l⟩ => l.toList
#align lists.to_list Lists.toList

/-- Predicate stating that a ZFA list is proper. -/
def IsList (l : Lists α) : Prop :=
  l.1
#align lists.is_list Lists.IsList

/-- Converts a `List` of ZFA lists to a ZFA list. -/
def ofList (l : List (Lists α)) : Lists α :=
  of' (Lists'.ofList l)
#align lists.of_list Lists.ofList

theorem isList_toList (l : List (Lists α)) : IsList (ofList l) :=
  Eq.refl _
#align lists.is_list_to_list Lists.isList_toList

theorem to_ofList (l : List (Lists α)) : toList (ofList l) = l := by simp [ofList, of']
                                                                     -- 🎉 no goals
#align lists.to_of_list Lists.to_ofList

theorem of_toList : ∀ {l : Lists α}, IsList l → ofList (toList l) = l
  | ⟨true, l⟩, _ => by simp_all [ofList, of']
                       -- 🎉 no goals
#align lists.of_to_list Lists.of_toList

instance : Inhabited (Lists α) :=
  ⟨of' Lists'.nil⟩

instance [DecidableEq α] : DecidableEq (Lists α) := by unfold Lists; infer_instance
                                                       -- ⊢ DecidableEq ((b : Bool) × Lists' α b)
                                                                     -- 🎉 no goals

instance [SizeOf α] : SizeOf (Lists α) := by unfold Lists; infer_instance
                                             -- ⊢ SizeOf ((b : Bool) × Lists' α b)
                                                           -- 🎉 no goals

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
  intros b l
  -- ⊢ PProd (C { fst := b, snd := l })
  induction' l with a b a l IH₁ IH
  · exact ⟨C0 _, ⟨⟩⟩
    -- 🎉 no goals
  · exact ⟨C1 _ D0, D0⟩
    -- 🎉 no goals
  · have : D (Lists'.cons' a l) := D1 ⟨_, _⟩ _ IH₁.1 IH.2
    -- ⊢ PProd (C { fst := true, snd := Lists'.cons' a l })
    exact ⟨C1 _ this, this⟩
    -- 🎉 no goals
#align lists.induction_mut Lists.inductionMut

/-- Membership of ZFA list. A ZFA list belongs to a proper ZFA list if it belongs to the latter as a
proper ZFA prelist. An atom has no members. -/
def mem (a : Lists α) : Lists α → Prop
  | ⟨false, _⟩ => False
  | ⟨_, l⟩ => a ∈ l
#align lists.mem Lists.mem

instance : Membership (Lists α) (Lists α) :=
  ⟨mem⟩

theorem isList_of_mem {a : Lists α} : ∀ {l : Lists α}, a ∈ l → IsList l
  | ⟨_, Lists'.nil⟩, _ => rfl
  | ⟨_, Lists'.cons' _ _⟩, _ => rfl
#align lists.is_list_of_mem Lists.isList_of_mem

theorem Equiv.antisymm_iff {l₁ l₂ : Lists' α true} : of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ := by
  refine' ⟨fun h => _, fun ⟨h₁, h₂⟩ => Equiv.antisymm h₁ h₂⟩
  -- ⊢ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁
  cases' h with _ _ _ h₁ h₂
  -- ⊢ l₁ ⊆ l₁ ∧ l₁ ⊆ l₁
  · simp [Lists'.Subset.refl]
    -- 🎉 no goals
  · exact ⟨h₁, h₂⟩
    -- 🎉 no goals
#align lists.equiv.antisymm_iff Lists.Equiv.antisymm_iff

attribute [refl] Equiv.refl

theorem equiv_atom {a} {l : Lists α} : atom a ~ l ↔ atom a = l :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Equiv.refl _⟩
               -- ⊢ atom a = atom a
                        -- 🎉 no goals
#align lists.equiv_atom Lists.equiv_atom

@[symm]
theorem Equiv.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  cases' h with _ _ _ h₁ h₂ <;> [rfl; exact Equiv.antisymm h₂ h₁]
  -- 🎉 no goals
#align lists.equiv.symm Lists.Equiv.symm

theorem Equiv.trans : ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ := by
  let trans := fun l₁ : Lists α => ∀ ⦃l₂ l₃⦄, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  -- ⊢ ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  suffices PProd (∀ l₁, trans l₁) (∀ (l : Lists' α true), ∀ l' ∈ l.toList, trans l') by exact this.1
  -- ⊢ PProd (∀ (l₁ : Lists α), trans l₁) (∀ (l : Lists' α true) (l' : Lists α), l' …
  apply inductionMut
  · intro a l₂ l₃ h₁ h₂
    -- ⊢ atom a ~ l₃
    rwa [← equiv_atom.1 h₁] at h₂
    -- 🎉 no goals
  · intro l₁ IH l₂ l₃ h₁ h₂
    -- ⊢ of' l₁ ~ l₃
    -- Porting note: Two 'have's are for saving the state.
    have h₁' := h₁
    -- ⊢ of' l₁ ~ l₃
    have h₂' := h₂
    -- ⊢ of' l₁ ~ l₃
    cases' h₁ with _ _ l₂
    -- ⊢ of' l₁ ~ l₃
    · exact h₂
      -- 🎉 no goals
    cases' h₂ with _ _ l₃
    -- ⊢ of' l₁ ~ { fst := true, snd := l₂ }
    · exact h₁'
      -- 🎉 no goals
    cases' Equiv.antisymm_iff.1 h₁' with hl₁ hr₁
    -- ⊢ of' l₁ ~ { fst := true, snd := l₃ }
    cases' Equiv.antisymm_iff.1 h₂' with hl₂ hr₂
    -- ⊢ of' l₁ ~ { fst := true, snd := l₃ }
    apply Equiv.antisymm_iff.2; constructor <;> apply Lists'.subset_def.2
    -- ⊢ l₁ ⊆ l₃ ∧ l₃ ⊆ l₁
                                -- ⊢ l₁ ⊆ l₃
                                                -- ⊢ ∀ (a : Lists α), a ∈ Lists'.toList l₁ → a ∈ l₃
                                                -- ⊢ ∀ (a : Lists α), a ∈ Lists'.toList l₃ → a ∈ l₁
    · intro a₁ m₁
      -- ⊢ a₁ ∈ l₃
      rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨a₂, m₂, e₁₂⟩
      -- ⊢ a₁ ∈ l₃
      rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨a₃, m₃, e₂₃⟩
      -- ⊢ a₁ ∈ l₃
      exact ⟨a₃, m₃, IH _ m₁ e₁₂ e₂₃⟩
      -- 🎉 no goals
    · intro a₃ m₃
      -- ⊢ a₃ ∈ l₁
      rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨a₂, m₂, e₃₂⟩
      -- ⊢ a₃ ∈ l₁
      rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨a₁, m₁, e₂₁⟩
      -- ⊢ a₃ ∈ l₁
      exact ⟨a₁, m₁, (IH _ m₁ e₂₁.symm e₃₂.symm).symm⟩
      -- 🎉 no goals
  · rintro _ ⟨⟩
    -- 🎉 no goals
  · intro a l IH₁ IH
    -- ⊢ ∀ (l' : Lists α), l' ∈ Lists'.toList (Lists'.cons a l) → trans l'
    -- Porting note: Previous code was:
    -- simpa [IH₁] using IH
    --
    -- Assumption fails.
    simp only [Lists'.toList, Sigma.eta, List.find?, List.mem_cons, forall_eq_or_imp]
    -- ⊢ (∀ ⦃l₂ l₃ : Lists α⦄, a ~ l₂ → l₂ ~ l₃ → a ~ l₃) ∧ ∀ (a : Lists α), a ∈ List …
    constructor
    -- ⊢ ∀ ⦃l₂ l₃ : Lists α⦄, a ~ l₂ → l₂ ~ l₃ → a ~ l₃
    · intros l₂ l₃ h₁ h₂
      -- ⊢ a ~ l₃
      exact IH₁ h₁ h₂
      -- 🎉 no goals
    · intros a h₁ l₂ l₃ h₂ h₃
      -- ⊢ a ~ l₃
      exact IH _ h₁ h₂ h₃
      -- 🎉 no goals
#align lists.equiv.trans Lists.Equiv.trans

instance instSetoidLists : Setoid (Lists α) :=
  ⟨(· ~ ·), Equiv.refl, @Equiv.symm _, @Equiv.trans _⟩

section Decidable

/-- Auxiliary function to prove termination of decidability checking -/
@[simp, deprecated] -- porting note: replaced by termination_by
def Equiv.decidableMeas :
    (PSum (Σ' _l₁ : Lists α, Lists α) <|
        PSum (Σ' _l₁ : Lists' α true, Lists' α true) (Σ' _a : Lists α, Lists' α true)) →
      ℕ
  | PSum.inl ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
  | PSum.inr <| PSum.inl ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
  | PSum.inr <| PSum.inr ⟨l₁, l₂⟩ => SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
#align lists.equiv.decidable_meas Lists.Equiv.decidableMeas

theorem sizeof_pos {b} (l : Lists' α b) : 0 < SizeOf.sizeOf l := by
  cases l <;> simp only [Lists'.atom.sizeOf_spec, Lists'.nil.sizeOf_spec, Lists'.cons'.sizeOf_spec,
    true_or, add_pos_iff]
#align lists.sizeof_pos Lists.sizeof_pos

theorem lt_sizeof_cons' {b} (a : Lists' α b) (l) :
    SizeOf.sizeOf (⟨b, a⟩ : Lists α) < SizeOf.sizeOf (Lists'.cons' a l) := by
  simp only [Sigma.mk.sizeOf_spec, Lists'.cons'.sizeOf_spec, lt_add_iff_pos_right]
  -- ⊢ 0 < sizeOf l
  apply sizeof_pos
  -- 🎉 no goals
#align lists.lt_sizeof_cons' Lists.lt_sizeof_cons'

variable [DecidableEq α]

mutual
  instance Equiv.decidable : ∀ l₁ l₂ : Lists α, Decidable (l₁ ~ l₂)
    | ⟨false, l₁⟩, ⟨false, l₂⟩ =>
      decidable_of_iff' (l₁ = l₂) <| by
        cases l₁
        -- ⊢ { fst := false, snd := Lists'.atom a✝ } ~ { fst := false, snd := l₂ } ↔ List …
        apply equiv_atom.trans
        -- ⊢ atom a✝ = { fst := false, snd := l₂ } ↔ Lists'.atom a✝ = l₂
        simp [atom]
        -- ⊢ { fst := false, snd := Lists'.atom a✝ } = { fst := false, snd := l₂ } ↔ List …
        constructor <;> (rintro ⟨rfl⟩; rfl)
        -- ⊢ { fst := false, snd := Lists'.atom a✝ } = { fst := false, snd := l₂ } → List …
                         -- ⊢ Lists'.atom a✝ = Lists'.atom a✝
                                       -- 🎉 no goals
                         -- ⊢ { fst := false, snd := Lists'.atom a✝ } = { fst := false, snd := Lists'.atom …
                                       -- 🎉 no goals
    | ⟨false, l₁⟩, ⟨true, l₂⟩ => isFalse <| by rintro ⟨⟩
                                               -- 🎉 no goals
    | ⟨true, l₁⟩, ⟨false, l₂⟩ => isFalse <| by rintro ⟨⟩
                                               -- 🎉 no goals
    | ⟨true, l₁⟩, ⟨true, l₂⟩ => by
      haveI : Decidable (l₁ ⊆ l₂) :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) :=
          by decreasing_tactic
        Subset.decidable l₁ l₂
      haveI : Decidable (l₂ ⊆ l₁) :=
        have : SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁ <
            SizeOf.sizeOf (⟨true, l₁⟩ : Lists α) + SizeOf.sizeOf (⟨true, l₂⟩ : Lists α) :=
          by decreasing_tactic
        Subset.decidable l₂ l₁
      exact decidable_of_iff' _ Equiv.antisymm_iff
      -- 🎉 no goals
  instance Subset.decidable  : ∀ l₁ l₂ : Lists' α true, Decidable (l₁ ⊆ l₂)
    | Lists'.nil, l₂ => isTrue Lists'.Subset.nil
    | @Lists'.cons' _ b a l₁, l₂ => by
      haveI :=
        have : sizeOf (⟨b, a⟩ : Lists α) < 1 + 1 + sizeOf a + sizeOf l₁ := by simp [sizeof_pos]
        mem.decidable ⟨b, a⟩ l₂
      haveI :=
        have : SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf (Lists'.cons' a l₁) + SizeOf.sizeOf l₂ :=
          by decreasing_tactic
        Subset.decidable l₁ l₂
      exact decidable_of_iff' _ (@Lists'.cons_subset _ ⟨_, _⟩ _ _)
      -- 🎉 no goals
  instance mem.decidable  : ∀ (a : Lists α) (l : Lists' α true), Decidable (a ∈ l)
    | a, Lists'.nil => isFalse <| by rintro ⟨_, ⟨⟩, _⟩
                                     -- 🎉 no goals
    | a, Lists'.cons' b l₂ => by
      haveI :=
        have : sizeOf (⟨_, b⟩ : Lists α) < 1 + 1 + sizeOf b + sizeOf l₂ := by simp [sizeof_pos]
        Equiv.decidable a ⟨_, b⟩
      haveI :=
        have :
          SizeOf.sizeOf a + SizeOf.sizeOf l₂ <
            SizeOf.sizeOf a + SizeOf.sizeOf (Lists'.cons' b l₂) :=
          by decreasing_tactic
        mem.decidable a l₂
      refine' decidable_of_iff' (a ~ ⟨_, b⟩ ∨ a ∈ l₂) _
      -- ⊢ a ∈ Lists'.cons' b l₂ ↔ a ~ { fst := b✝, snd := b } ∨ a ∈ l₂
      rw [← Lists'.mem_cons]; rfl
      -- ⊢ a ∈ Lists'.cons' b l₂ ↔ a ∈ Lists'.cons { fst := b✝, snd := b } l₂
                              -- 🎉 no goals
end
termination_by
  Subset.decidable x y => sizeOf x + sizeOf y
  Equiv.decidable x y => sizeOf x + sizeOf y
  mem.decidable x y => sizeOf x + sizeOf y
#align lists.equiv.decidable Lists.Equiv.decidable
#align lists.subset.decidable Lists.Subset.decidable
#align lists.mem.decidable Lists.mem.decidable

end Decidable

end Lists

namespace Lists'

theorem mem_equiv_left {l : Lists' α true} : ∀ {a a'}, a ~ a' → (a ∈ l ↔ a' ∈ l) :=
  suffices ∀ {a a'}, a ~ a' → a ∈ l → a' ∈ l from fun e => ⟨this e, this e.symm⟩
  fun e₁ ⟨_, m₃, e₂⟩ => ⟨_, m₃, e₁.symm.trans e₂⟩
#align lists'.mem_equiv_left Lists'.mem_equiv_left

theorem mem_of_subset {a} {l₁ l₂ : Lists' α true} (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂
  | ⟨_, m, e⟩ => (mem_equiv_left e).2 (mem_of_subset' s m)
#align lists'.mem_of_subset Lists'.mem_of_subset

theorem Subset.trans {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  subset_def.2 fun _ m₁ => mem_of_subset h₂ <| mem_of_subset' h₁ m₁
#align lists'.subset.trans Lists'.Subset.trans

end Lists'

/-- `Finsets` are defined via equivalence classes of `Lists` -/
def Finsets (α : Type*) :=
  Quotient (@Lists.instSetoidLists α)
#align finsets Finsets

namespace Finsets

instance : EmptyCollection (Finsets α) :=
  ⟨⟦Lists.of' Lists'.nil⟧⟩

instance : Inhabited (Finsets α) :=
  ⟨∅⟩

instance [DecidableEq α] : DecidableEq (Finsets α) := by
  unfold Finsets
  -- ⊢ DecidableEq (Quotient Lists.instSetoidLists)
  -- porting notes: infer_instance does not work for some reason
  exact (Quotient.decidableEq (d := fun _ _ => Lists.Equiv.decidable _ _))
  -- 🎉 no goals

end Finsets
