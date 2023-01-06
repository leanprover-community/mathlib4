/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.lists
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
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

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is\nequivalent as a ZFA list to this ZFA list. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.implicitBinder "{" [`b] [] "}")]
       (Term.typeSpec
        ":"
        (Term.app `Membership [(Term.app `Lists [`α]) (Term.app `Lists' [`α `b])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a `l]
           []
           "=>"
           (Std.ExtendedBinder.«term∃__,_»
            "∃"
            (Lean.binderIdent `a')
            («binderTerm∈_» "∈" (Term.proj `l "." `toList))
            ","
            (SetTheory.Lists.«term_~_» `a " ~ " `a'))))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `l]
          []
          "=>"
          (Std.ExtendedBinder.«term∃__,_»
           "∃"
           (Lean.binderIdent `a')
           («binderTerm∈_» "∈" (Term.proj `l "." `toList))
           ","
           (SetTheory.Lists.«term_~_» `a " ~ " `a'))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `l]
        []
        "=>"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `a')
         («binderTerm∈_» "∈" (Term.proj `l "." `toList))
         ","
         (SetTheory.Lists.«term_~_» `a " ~ " `a'))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `a')
       («binderTerm∈_» "∈" (Term.proj `l "." `toList))
       ","
       (SetTheory.Lists.«term_~_» `a " ~ " `a'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SetTheory.Lists.«term_~_» `a " ~ " `a')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    ZFA prelist membership. A ZFA list is in a ZFA prelist if some element of this ZFA prelist is
    equivalent as a ZFA list to this ZFA list. -/
  instance { b } : Membership Lists α Lists' α b := ⟨ fun a l => ∃ a' ∈ l . toList , a ~ a' ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_def [])
      (Command.declSig
       [(Term.implicitBinder "{" [`b `a] [] "}")
        (Term.implicitBinder "{" [`l] [":" (Term.app `Lists' [`α `b])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `a "∈" `l)
         "↔"
         (Std.ExtendedBinder.«term∃__,_»
          "∃"
          (Lean.binderIdent `a')
          («binderTerm∈_» "∈" (Term.proj `l "." `toList))
          ","
          (SetTheory.Lists.«term_~_» `a " ~ " `a')))))
      (Command.declValSimple ":=" `Iff.rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `a "∈" `l)
       "↔"
       (Std.ExtendedBinder.«term∃__,_»
        "∃"
        (Lean.binderIdent `a')
        («binderTerm∈_» "∈" (Term.proj `l "." `toList))
        ","
        (SetTheory.Lists.«term_~_» `a " ~ " `a')))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `a')
       («binderTerm∈_» "∈" (Term.proj `l "." `toList))
       ","
       (SetTheory.Lists.«term_~_» `a " ~ " `a'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SetTheory.Lists.«term_~_» `a " ~ " `a')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem mem_def { b a } { l : Lists' α b } : a ∈ l ↔ ∃ a' ∈ l . toList , a ~ a' := Iff.rfl
#align lists'.mem_def Lists'.mem_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_cons [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `y `l] [] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `a "∈" (Term.app (Term.explicit "@" `cons) [`α `y `l]))
         "↔"
         («term_∨_» (SetTheory.Lists.«term_~_» `a " ~ " `y) "∨" («term_∈_» `a "∈" `l)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `mem_def)
              ","
              (Tactic.simpLemma [] [] `or_and_right)
              ","
              (Tactic.simpLemma [] [] `exists_or)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `mem_def)
             ","
             (Tactic.simpLemma [] [] `or_and_right)
             ","
             (Tactic.simpLemma [] [] `exists_or)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `mem_def)
         ","
         (Tactic.simpLemma [] [] `or_and_right)
         ","
         (Tactic.simpLemma [] [] `exists_or)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_or
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `or_and_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `a "∈" (Term.app (Term.explicit "@" `cons) [`α `y `l]))
       "↔"
       («term_∨_» (SetTheory.Lists.«term_~_» `a " ~ " `y) "∨" («term_∈_» `a "∈" `l)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» (SetTheory.Lists.«term_~_» `a " ~ " `y) "∨" («term_∈_» `a "∈" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `a "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      (SetTheory.Lists.«term_~_» `a " ~ " `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    mem_cons
    { a y l } : a ∈ @ cons α y l ↔ a ~ y ∨ a ∈ l
    := by simp [ mem_def , or_and_right , exists_or ]
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

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.antisymm_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`l₁ `l₂] [":" (Term.app `Lists' [`α `true])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (SetTheory.Lists.«term_~_» (Term.app `of' [`l₁]) " ~ " (Term.app `of' [`l₂]))
         "↔"
         («term_∧_» («term_⊆_» `l₁ "⊆" `l₂) "∧" («term_⊆_» `l₂ "⊆" `l₁)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
                []
                "=>"
                (Term.app `equiv.antisymm [`h₁ `h₂])))]
             "⟩"))
           []
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent `h₁)
              (Lean.binderIdent `h₂)]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `Lists'.Subset.refl)] "]"]
              [])])
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩"))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
               []
               "=>"
               (Term.app `equiv.antisymm [`h₁ `h₂])))]
            "⟩"))
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `h)]
           []
           ["with"
            [(Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent (Term.hole "_"))
             (Lean.binderIdent `h₁)
             (Lean.binderIdent `h₂)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `Lists'.Subset.refl)] "]"]
             [])])
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Lists'.Subset.refl)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Lists'.Subset.refl)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Lists'.Subset.refl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `h₁)
         (Lean.binderIdent `h₂)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
           []
           "=>"
           (Term.app `equiv.antisymm [`h₁ `h₂])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
          []
          "=>"
          (Term.app `equiv.antisymm [`h₁ `h₂])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
        []
        "=>"
        (Term.app `equiv.antisymm [`h₁ `h₂])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `equiv.antisymm [`h₁ `h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `equiv.antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (SetTheory.Lists.«term_~_» (Term.app `of' [`l₁]) " ~ " (Term.app `of' [`l₂]))
       "↔"
       («term_∧_» («term_⊆_» `l₁ "⊆" `l₂) "∧" («term_⊆_» `l₂ "⊆" `l₁)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» («term_⊆_» `l₁ "⊆" `l₂) "∧" («term_⊆_» `l₂ "⊆" `l₁))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_» `l₂ "⊆" `l₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l₁
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_⊆_» `l₁ "⊆" `l₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l₁
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (SetTheory.Lists.«term_~_» (Term.app `of' [`l₁]) " ~ " (Term.app `of' [`l₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Equiv.antisymm_iff
  { l₁ l₂ : Lists' α true } : of' l₁ ~ of' l₂ ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁
  :=
    by
      refine' ⟨ fun h => _ , fun ⟨ h₁ , h₂ ⟩ => equiv.antisymm h₁ h₂ ⟩
        cases' h with _ _ _ h₁ h₂
        · simp [ Lists'.Subset.refl ]
        ;
        · exact ⟨ h₁ , h₂ ⟩
#align lists.equiv.antisymm_iff Lists.Equiv.antisymm_iff

attribute [refl] Equiv.refl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `equiv_atom [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [] "}")
        (Term.implicitBinder "{" [`l] [":" (Term.app `Lists [`α])] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (SetTheory.Lists.«term_~_» (Term.app `atom [`a]) " ~ " `l)
         "↔"
         («term_=_» (Term.app `atom [`a]) "=" `l))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
                "<;>"
                (Tactic.tacticRfl "rfl"))])))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.subst `h "▸" [(Term.app `Equiv.refl [(Term.hole "_")])])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
               "<;>"
               (Tactic.tacticRfl "rfl"))])))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.subst `h "▸" [(Term.app `Equiv.refl [(Term.hole "_")])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`h] [] "=>" (Term.subst `h "▸" [(Term.app `Equiv.refl [(Term.hole "_")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst `h "▸" [(Term.app `Equiv.refl [(Term.hole "_")])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
             "<;>"
             (Tactic.tacticRfl "rfl"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (SetTheory.Lists.«term_~_» (Term.app `atom [`a]) " ~ " `l)
       "↔"
       («term_=_» (Term.app `atom [`a]) "=" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `atom [`a]) "=" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `atom [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `atom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (SetTheory.Lists.«term_~_» (Term.app `atom [`a]) " ~ " `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  equiv_atom
  { a } { l : Lists α } : atom a ~ l ↔ atom a = l
  := ⟨ fun h => by cases h <;> rfl , fun h => h ▸ Equiv.refl _ ⟩
#align lists.equiv_atom Lists.equiv_atom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.symm [])
      (Command.declSig
       [(Term.implicitBinder "{" [`l₁ `l₂] [":" (Term.app `Lists [`α])] "}")
        (Term.explicitBinder "(" [`h] [":" (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)] [] ")")]
       (Term.typeSpec ":" (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₁)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.seq_focus
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `h)]
             []
             ["with"
              [(Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent `h₁)
               (Lean.binderIdent `h₂)]])
            "<;>"
            "["
            [(Tactic.tacticRfl "rfl")
             ","
             (Tactic.exact "exact" (Term.app `equiv.antisymm [`h₂ `h₁]))]
            "]")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.seq_focus
           (Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `h)]
            []
            ["with"
             [(Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent (Term.hole "_"))
              (Lean.binderIdent `h₁)
              (Lean.binderIdent `h₂)]])
           "<;>"
           "["
           [(Tactic.tacticRfl "rfl")
            ","
            (Tactic.exact "exact" (Term.app `equiv.antisymm [`h₂ `h₁]))]
           "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] `h)]
        []
        ["with"
         [(Lean.binderIdent (Term.hole "_"))
          (Lean.binderIdent (Term.hole "_"))
          (Lean.binderIdent (Term.hole "_"))
          (Lean.binderIdent `h₁)
          (Lean.binderIdent `h₂)]])
       "<;>"
       "["
       [(Tactic.tacticRfl "rfl") "," (Tactic.exact "exact" (Term.app `equiv.antisymm [`h₂ `h₁]))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `equiv.antisymm [`h₂ `h₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `equiv.antisymm [`h₂ `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `equiv.antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `h₁)
         (Lean.binderIdent `h₂)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₁)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Equiv.symm
  { l₁ l₂ : Lists α } ( h : l₁ ~ l₂ ) : l₂ ~ l₁
  := by cases' h with _ _ _ h₁ h₂ <;> [ rfl , exact equiv.antisymm h₂ h₁ ]
#align lists.equiv.symm Lists.Equiv.symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Equiv.trans [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`l₁ `l₂ `l₃] [":" (Term.app `Lists [`α])] "}")]
         []
         ","
         (Term.arrow
          (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
          "→"
          (Term.arrow
           (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
           "→"
           (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `trans
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`l₁]
                [(Term.typeSpec ":" (Term.app `Lists [`α]))]
                "=>"
                (Term.forall
                 "∀"
                 [(Term.strictImplicitBinder "⦃" [`l₂ `l₃] [] "⦄")]
                 []
                 ","
                 (Term.arrow
                  (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
                  "→"
                  (Term.arrow
                   (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
                   "→"
                   (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃)))))))))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.app
              `PProd
              [(Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
               (Term.forall
                "∀"
                [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
                []
                ","
                (Std.ExtendedBinder.«term∀__,_»
                 "∀"
                 (Lean.binderIdent `l')
                 («binderTerm∈_» "∈" (Term.proj `l "." `toList))
                 ","
                 (Term.app `trans [`l'])))])
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.exact "exact" (Term.proj `this "." (fieldIdx "1")))])))))
           []
           (Tactic.apply "apply" `induction_mut)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`a `l₂ `l₃ `h₁ `h₂])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app (Term.proj `equiv_atom "." (fieldIdx "1")) [`h₁]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`l₁ `IH `l₂ `l₃ `h₁ `h₂])
             []
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `h₁)]
              []
              ["with"
               [(Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent `l₂)]])
             []
             (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₂)])
             []
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `h₂)]
              []
              ["with"
               [(Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent (Term.hole "_"))
                (Lean.binderIdent `l₃)]])
             []
             (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₁)])
             []
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget
                []
                (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₁]))]
              []
              ["with" [(Lean.binderIdent `hl₁) (Lean.binderIdent `hr₁)]])
             []
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget
                []
                (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₂]))]
              []
              ["with" [(Lean.binderIdent `hl₂) (Lean.binderIdent `hr₂)]])
             []
             (Tactic.«tactic_<;>_»
              (Tactic.«tactic_<;>_»
               (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
               "<;>"
               (Tactic.constructor "constructor"))
              "<;>"
              (Tactic.apply "apply" (Term.proj `Lists'.subset_def "." (fieldIdx "2"))))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`a₁ `m₁])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁₂)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₃)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₃)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₃)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])]
                 "⟩"))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`a₃ `m₃])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃₂)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₁)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [`a₁
                  ","
                  `m₁
                  ","
                  (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
                 "⟩"))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`a `l `IH₁ `IH₂])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `IH₁)] "]")]
               ["using" `IH₂]))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `trans
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`l₁]
               [(Term.typeSpec ":" (Term.app `Lists [`α]))]
               "=>"
               (Term.forall
                "∀"
                [(Term.strictImplicitBinder "⦃" [`l₂ `l₃] [] "⦄")]
                []
                ","
                (Term.arrow
                 (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
                 "→"
                 (Term.arrow
                  (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
                  "→"
                  (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃)))))))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.app
             `PProd
             [(Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
              (Term.forall
               "∀"
               [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
               []
               ","
               (Std.ExtendedBinder.«term∀__,_»
                "∀"
                (Lean.binderIdent `l')
                («binderTerm∈_» "∈" (Term.proj `l "." `toList))
                ","
                (Term.app `trans [`l'])))])
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.exact "exact" (Term.proj `this "." (fieldIdx "1")))])))))
          []
          (Tactic.apply "apply" `induction_mut)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`a `l₂ `l₃ `h₁ `h₂])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app (Term.proj `equiv_atom "." (fieldIdx "1")) [`h₁]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`l₁ `IH `l₂ `l₃ `h₁ `h₂])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `h₁)]
             []
             ["with"
              [(Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent `l₂)]])
            []
            (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₂)])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `h₂)]
             []
             ["with"
              [(Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent (Term.hole "_"))
               (Lean.binderIdent `l₃)]])
            []
            (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₁)])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget
               []
               (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₁]))]
             []
             ["with" [(Lean.binderIdent `hl₁) (Lean.binderIdent `hr₁)]])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget
               []
               (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₂]))]
             []
             ["with" [(Lean.binderIdent `hl₂) (Lean.binderIdent `hr₂)]])
            []
            (Tactic.«tactic_<;>_»
             (Tactic.«tactic_<;>_»
              (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
              "<;>"
              (Tactic.constructor "constructor"))
             "<;>"
             (Tactic.apply "apply" (Term.proj `Lists'.subset_def "." (fieldIdx "2"))))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`a₁ `m₁])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁₂)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₃)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₃)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₃)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`a₃ `m₃])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃₂)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₁)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`a₁
                 ","
                 `m₁
                 ","
                 (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
                "⟩"))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`a `l `IH₁ `IH₂])
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `IH₁)] "]")]
              ["using" `IH₂]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a `l `IH₁ `IH₂])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `IH₁)] "]")]
          ["using" `IH₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `IH₁)] "]")]
        ["using" `IH₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `l `IH₁ `IH₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IH₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IH₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`l₁ `IH `l₂ `l₃ `h₁ `h₂])
        []
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] `h₁)]
         []
         ["with"
          [(Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent `l₂)]])
        []
        (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₂)])
        []
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] `h₂)]
         []
         ["with"
          [(Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent (Term.hole "_"))
           (Lean.binderIdent `l₃)]])
        []
        (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₁)])
        []
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₁]))]
         []
         ["with" [(Lean.binderIdent `hl₁) (Lean.binderIdent `hr₁)]])
        []
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₂]))]
         []
         ["with" [(Lean.binderIdent `hl₂) (Lean.binderIdent `hr₂)]])
        []
        (Tactic.«tactic_<;>_»
         (Tactic.«tactic_<;>_»
          (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
          "<;>"
          (Tactic.constructor "constructor"))
         "<;>"
         (Tactic.apply "apply" (Term.proj `Lists'.subset_def "." (fieldIdx "2"))))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`a₁ `m₁])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁₂)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₃)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₃)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₃)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])]
            "⟩"))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`a₃ `m₃])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃₂)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₁)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`a₁
             ","
             `m₁
             ","
             (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
            "⟩"))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a₃ `m₃])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃₂)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₁)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`a₁
           ","
           `m₁
           ","
           (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`a₁
         ","
         `m₁
         ","
         (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`a₁
        ","
        `m₁
        ","
        (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₃₂.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e₂₁.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `IH [(Term.hole "_") `m₁ `e₂₁.symm `e₃₂.symm])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₁)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lists'.mem_of_subset' [`hr₁ `m₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hr₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lists'.mem_of_subset'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃₂)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lists'.mem_of_subset' [`hr₂ `m₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hr₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lists'.mem_of_subset'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a₃ `m₃])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a₁ `m₁])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁₂)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₃)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₃)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₃)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a₃ "," `m₃ "," (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IH [(Term.hole "_") `m₁ `e₁₂ `e₂₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e₁₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₃)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₃)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂₃)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lists'.mem_of_subset' [`hl₂ `m₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hl₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lists'.mem_of_subset'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `m₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁₂)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lists'.mem_of_subset' [`hl₁ `m₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hl₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lists'.mem_of_subset'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a₁ `m₁])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
        "<;>"
        (Tactic.constructor "constructor"))
       "<;>"
       (Tactic.apply "apply" (Term.proj `Lists'.subset_def "." (fieldIdx "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj `Lists'.subset_def "." (fieldIdx "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `Lists'.subset_def "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Lists'.subset_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
       "<;>"
       (Tactic.constructor "constructor"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.apply "apply" (Term.proj `equiv.antisymm_iff "." (fieldIdx "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `equiv.antisymm_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `equiv.antisymm_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₂]))]
       []
       ["with" [(Lean.binderIdent `hl₂) (Lean.binderIdent `hr₂)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `equiv.antisymm_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `equiv.antisymm_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₁]))]
       []
       ["with" [(Lean.binderIdent `hl₁) (Lean.binderIdent `hr₁)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `equiv.antisymm_iff "." (fieldIdx "1")) [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `equiv.antisymm_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `equiv.antisymm_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₁)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h₂)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `l₃)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.exact "exact" `h₂)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `h₁)]
       []
       ["with"
        [(Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent (Term.hole "_"))
         (Lean.binderIdent `l₂)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`l₁ `IH `l₂ `l₃ `h₁ `h₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IH
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a `l₂ `l₃ `h₁ `h₂])
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app (Term.proj `equiv_atom "." (fieldIdx "1")) [`h₁]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app (Term.proj `equiv_atom "." (fieldIdx "1")) [`h₁]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `equiv_atom "." (fieldIdx "1")) [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `equiv_atom "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `equiv_atom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `l₂ `l₃ `h₁ `h₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `induction_mut)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `induction_mut
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.app
         `PProd
         [(Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
           []
           ","
           (Std.ExtendedBinder.«term∀__,_»
            "∀"
            (Lean.binderIdent `l')
            («binderTerm∈_» "∈" (Term.proj `l "." `toList))
            ","
            (Term.app `trans [`l'])))])
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.exact "exact" (Term.proj `this "." (fieldIdx "1")))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj `this "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `this "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PProd
       [(Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
        (Term.forall
         "∀"
         [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
         []
         ","
         (Std.ExtendedBinder.«term∀__,_»
          "∀"
          (Lean.binderIdent `l')
          («binderTerm∈_» "∈" (Term.proj `l "." `toList))
          ","
          (Term.app `trans [`l'])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
       []
       ","
       (Std.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `l')
        («binderTerm∈_» "∈" (Term.proj `l "." `toList))
        ","
        (Term.app `trans [`l'])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `l')
       («binderTerm∈_» "∈" (Term.proj `l "." `toList))
       ","
       (Term.app `trans [`l']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trans [`l'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `l "." `toList)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lists' [`α `tt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lists'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall
      "∀"
      [(Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `tt])] [] ")")]
      []
      ","
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `l')
       («binderTerm∈_» "∈" (Term.proj `l "." `toList))
       ","
       (Term.app `trans [`l'])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `trans [`l₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.forall "∀" [`l₁] [] "," (Term.app `trans [`l₁]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PProd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `trans
         []
         []
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`l₁]
           [(Term.typeSpec ":" (Term.app `Lists [`α]))]
           "=>"
           (Term.forall
            "∀"
            [(Term.strictImplicitBinder "⦃" [`l₂ `l₃] [] "⦄")]
            []
            ","
            (Term.arrow
             (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
             "→"
             (Term.arrow
              (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
              "→"
              (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃)))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`l₁]
        [(Term.typeSpec ":" (Term.app `Lists [`α]))]
        "=>"
        (Term.forall
         "∀"
         [(Term.strictImplicitBinder "⦃" [`l₂ `l₃] [] "⦄")]
         []
         ","
         (Term.arrow
          (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
          "→"
          (Term.arrow
           (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
           "→"
           (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`l₂ `l₃] [] "⦄")]
       []
       ","
       (Term.arrow
        (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
        "→"
        (Term.arrow
         (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
         "→"
         (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)
       "→"
       (Term.arrow
        (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
        "→"
        (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (SetTheory.Lists.«term_~_» `l₂ " ~ " `l₃)
       "→"
       (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SetTheory.Lists.«term_~_» `l₁ " ~ " `l₃)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Equiv.trans
  : ∀ { l₁ l₂ l₃ : Lists α } , l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
  :=
    by
      let trans := fun l₁ : Lists α => ∀ ⦃ l₂ l₃ ⦄ , l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
        suffices
          PProd ∀ l₁ , trans l₁ ∀ ( l : Lists' α tt ) , ∀ l' ∈ l . toList , trans l'
            by exact this . 1
        apply induction_mut
        · intro a l₂ l₃ h₁ h₂ rwa [ ← equiv_atom . 1 h₁ ] at h₂
        ·
          intro l₁ IH l₂ l₃ h₁ h₂
            cases' h₁ with _ _ l₂
            · exact h₂
            cases' h₂ with _ _ l₃
            · exact h₁
            cases' equiv.antisymm_iff . 1 h₁ with hl₁ hr₁
            cases' equiv.antisymm_iff . 1 h₂ with hl₂ hr₂
            apply equiv.antisymm_iff . 2 <;> constructor <;> apply Lists'.subset_def . 2
            ·
              intro a₁ m₁
                rcases Lists'.mem_of_subset' hl₁ m₁ with ⟨ a₂ , m₂ , e₁₂ ⟩
                rcases Lists'.mem_of_subset' hl₂ m₂ with ⟨ a₃ , m₃ , e₂₃ ⟩
                exact ⟨ a₃ , m₃ , IH _ m₁ e₁₂ e₂₃ ⟩
            ·
              intro a₃ m₃
                rcases Lists'.mem_of_subset' hr₂ m₃ with ⟨ a₂ , m₂ , e₃₂ ⟩
                rcases Lists'.mem_of_subset' hr₁ m₂ with ⟨ a₁ , m₁ , e₂₁ ⟩
                exact ⟨ a₁ , m₁ , IH _ m₁ e₂₁.symm e₃₂.symm . symm ⟩
        · rintro _ ⟨ ⟩
        · intro a l IH₁ IH₂ simpa [ IH₁ ] using IH₂
#align lists.equiv.trans Lists.Equiv.trans

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Setoid [(Term.app `Lists [`α])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.paren "(" (SetTheory.Lists.«term_~_» (Term.cdot "·") " ~ " (Term.cdot "·")) ")")
         ","
         `Equiv.refl
         ","
         (Term.app (Term.explicit "@" `Equiv.symm) [(Term.hole "_")])
         ","
         (Term.app (Term.explicit "@" `Equiv.trans) [(Term.hole "_")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.paren "(" (SetTheory.Lists.«term_~_» (Term.cdot "·") " ~ " (Term.cdot "·")) ")")
        ","
        `Equiv.refl
        ","
        (Term.app (Term.explicit "@" `Equiv.symm) [(Term.hole "_")])
        ","
        (Term.app (Term.explicit "@" `Equiv.trans) [(Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `Equiv.trans) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Equiv.trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `Equiv.symm) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Equiv.symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.refl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" (SetTheory.Lists.«term_~_» (Term.cdot "·") " ~ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SetTheory.Lists.«term_~_» (Term.cdot "·") " ~ " (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Setoid Lists α := ⟨ ( · ~ · ) , Equiv.refl , @ Equiv.symm _ , @ Equiv.trans _ ⟩

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
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.mutual
     "mutual"
     [(Command.declaration
       (Command.declModifiers
        []
        [(Term.attributes
          "@["
          [(Term.attrInstance (Term.attrKind []) (Attr.instance "instance" []))]
          "]")]
        []
        []
        []
        [])
       (Command.def
        "def"
        (Command.declId `Equiv.decidable [])
        (Command.optDeclSig
         [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`l₁ `l₂]
            [(Term.typeSpec ":" (Term.app `Lists [`α]))]
            ","
            (Term.app `Decidable [(SetTheory.Lists.«term_~_» `l₁ " ~ " `l₂)])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[(Term.anonymousCtor "⟨" [`ff "," `l₁] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`ff "," `l₂] "⟩")]]
             "=>"
             («term_<|_»
              (Term.app `decidable_of_iff' [(«term_=_» `l₁ "=" `l₂)])
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.cases "cases" [(Tactic.casesTarget [] `l₁)] [] [])
                   "<;>"
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `equiv_atom.trans
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           []
                           ["[" [(Tactic.simpLemma [] [] `atom)] "]"]
                           [])])))])))])))))
            (Term.matchAlt
             "|"
             [[(Term.anonymousCtor "⟨" [`ff "," `l₁] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`tt "," `l₂] "⟩")]]
             "=>"
             («term_<|_»
              `is_false
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
                   [])])))))
            (Term.matchAlt
             "|"
             [[(Term.anonymousCtor "⟨" [`tt "," `l₁] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`ff "," `l₂] "⟩")]]
             "=>"
             («term_<|_»
              `is_false
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩"))]
                   [])])))))
            (Term.matchAlt
             "|"
             [[(Term.anonymousCtor "⟨" [`tt "," `l₁] "⟩")
               ","
               (Term.anonymousCtor "⟨" [`tt "," `l₂] "⟩")]]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`l₁])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))
                          "<"
                          («term_+_»
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [`tt "," `l₁] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")])
                           "+"
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [`tt "," `l₂] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")]))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.RunCmd.runTac
                            "run_tac"
                            (Term.doSeqIndent
                             [(Term.doSeqItem (Term.doExpr `default_dec_tac) [])]))])))))
                     []
                     (Term.app `subset.decidable [`l₁ `l₂])))))
                 []
                 (Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`l₂])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₁]))
                          "<"
                          («term_+_»
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [`tt "," `l₁] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")])
                           "+"
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [`tt "," `l₂] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")]))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.RunCmd.runTac
                            "run_tac"
                            (Term.doSeqIndent
                             [(Term.doSeqItem (Term.doExpr `default_dec_tac) [])]))])))))
                     []
                     (Term.app `subset.decidable [`l₂ `l₁])))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `decidable_of_iff' [(Term.hole "_") `equiv.antisymm_iff]))]))))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        []
        [(Term.attributes
          "@["
          [(Term.attrInstance (Term.attrKind []) (Attr.instance "instance" []))]
          "]")]
        []
        []
        []
        [])
       (Command.def
        "def"
        (Command.declId `Subset.decidable [])
        (Command.optDeclSig
         [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`l₁ `l₂]
            [(Term.typeSpec ":" (Term.app `Lists' [`α `true]))]
            ","
            (Term.app `Decidable [(«term_⊆_» `l₁ "⊆" `l₂)])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt "|" [[`Lists'.nil "," `l₂]] "=>" (Term.app `isTrue [`Subset.nil]))
            (Term.matchAlt
             "|"
             [[(Term.app (Term.explicit "@" `Lists'.cons') [(Term.hole "_") `b `a `l₁]) "," `l₂]]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [`b "," `a] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))
                          "<"
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`a `l₁])])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))))]
                       ":="
                       (Term.app
                        `add_lt_add_right
                        [(Term.app `lt_sizeof_cons' [(Term.hole "_") (Term.hole "_")])
                         (Term.hole "_")])))
                     []
                     (Term.app `mem.decidable [(Term.anonymousCtor "⟨" [`b "," `a] "⟩") `l₂])))))
                 []
                 (Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`l₁])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))
                          "<"
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`a `l₁])])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.RunCmd.runTac
                            "run_tac"
                            (Term.doSeqIndent
                             [(Term.doSeqItem (Term.doExpr `default_dec_tac) [])]))])))))
                     []
                     (Term.app `subset.decidable [`l₁ `l₂])))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `decidable_of_iff'
                   [(Term.hole "_")
                    (Term.app
                     (Term.explicit "@" `Lists'.cons_subset)
                     [(Term.hole "_")
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                      (Term.hole "_")
                      (Term.hole "_")])]))]))))])
          []))
        []
        []
        []))
      (Command.declaration
       (Command.declModifiers
        []
        [(Term.attributes
          "@["
          [(Term.attrInstance (Term.attrKind []) (Attr.instance "instance" []))]
          "]")]
        []
        []
        []
        [])
       (Command.def
        "def"
        (Command.declId `Mem.decidable [])
        (Command.optDeclSig
         [(Term.instBinder "[" [] (Term.app `DecidableEq [`α]) "]")]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.explicitBinder "(" [`a] [":" (Term.app `Lists [`α])] [] ")")
             (Term.explicitBinder "(" [`l] [":" (Term.app `Lists' [`α `true])] [] ")")]
            []
            ","
            (Term.app `Decidable [(«term_∈_» `a "∈" `l)])))])
        (Command.declValEqns
         (Term.matchAltsWhereDecls
          (Term.matchAlts
           [(Term.matchAlt
             "|"
             [[`a "," `Lists'.nil]]
             "=>"
             («term_<|_»
              `is_false
              "<|"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                        [])]
                      "⟩"))]
                   [])])))))
            (Term.matchAlt
             "|"
             [[`a "," (Term.app `Lists'.cons' [`b `l₂])]]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`a])
                           "+"
                           (Term.app
                            `SizeOf.sizeOf
                            [(Term.typeAscription
                              "("
                              (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩")
                              ":"
                              [(Term.app `Lists [`α])]
                              ")")]))
                          "<"
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`a])
                           "+"
                           (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`b `l₂])]))))]
                       ":="
                       (Term.app
                        `add_lt_add_left
                        [(Term.app `lt_sizeof_cons' [(Term.hole "_") (Term.hole "_")])
                         (Term.hole "_")])))
                     []
                     (Term.app
                      `equiv.decidable
                      [`a (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩")])))))
                 []
                 (Std.Tactic.tacticHaveI_
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.have
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_<_»
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`a])
                           "+"
                           (Term.app `SizeOf.sizeOf [`l₂]))
                          "<"
                          («term_+_»
                           (Term.app `SizeOf.sizeOf [`a])
                           "+"
                           (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`b `l₂])]))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.RunCmd.runTac
                            "run_tac"
                            (Term.doSeqIndent
                             [(Term.doSeqItem (Term.doExpr `default_dec_tac) [])]))])))))
                     []
                     (Term.app `mem.decidable [`a `l₂])))))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `decidable_of_iff'
                   [(«term_∨_»
                     (SetTheory.Lists.«term_~_»
                      `a
                      " ~ "
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
                     "∨"
                     («term_∈_» `a "∈" `l₂))
                    (Term.hole "_")]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Lists'.mem_cons)]
                   "]")
                  [])
                 ";"
                 (Tactic.tacticRfl "rfl")]))))])
          []))
        []
        []
        []))]
     "end"
     [(Command.terminationByCore
       "termination_by'"
       (Command.terminationHint1
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_") "," (Term.app `measure_wf [`equiv.decidable_meas])]
         "⟩")))]
     [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.terminationByCore', expected 'Lean.Parser.Command.terminationBy'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.terminationHint1', expected 'Lean.Parser.Command.terminationHintMany'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_") "," (Term.app `measure_wf [`equiv.decidable_meas])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `measure_wf [`equiv.decidable_meas])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `equiv.decidable_meas
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `measure_wf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   («term_+_»
                    (Term.app `SizeOf.sizeOf [`a])
                    "+"
                    (Term.app
                     `SizeOf.sizeOf
                     [(Term.typeAscription
                       "("
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩")
                       ":"
                       [(Term.app `Lists [`α])]
                       ")")]))
                   "<"
                   («term_+_»
                    (Term.app `SizeOf.sizeOf [`a])
                    "+"
                    (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`b `l₂])]))))]
                ":="
                (Term.app
                 `add_lt_add_left
                 [(Term.app `lt_sizeof_cons' [(Term.hole "_") (Term.hole "_")]) (Term.hole "_")])))
              []
              (Term.app
               `equiv.decidable
               [`a (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩")])))))
          []
          (Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.have
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   («term_+_» (Term.app `SizeOf.sizeOf [`a]) "+" (Term.app `SizeOf.sizeOf [`l₂]))
                   "<"
                   («term_+_»
                    (Term.app `SizeOf.sizeOf [`a])
                    "+"
                    (Term.app `SizeOf.sizeOf [(Term.app `Lists'.cons' [`b `l₂])]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.RunCmd.runTac
                     "run_tac"
                     (Term.doSeqIndent [(Term.doSeqItem (Term.doExpr `default_dec_tac) [])]))])))))
              []
              (Term.app `mem.decidable [`a `l₂])))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `decidable_of_iff'
            [(«term_∨_»
              (SetTheory.Lists.«term_~_»
               `a
               " ~ "
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
              "∨"
              («term_∈_» `a "∈" `l₂))
             (Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Lists'.mem_cons)]
            "]")
           [])
          ";"
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Lists'.mem_cons)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Lists'.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `decidable_of_iff'
        [(«term_∨_»
          (SetTheory.Lists.«term_~_» `a " ~ " (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
          "∨"
          («term_∈_» `a "∈" `l₂))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `decidable_of_iff'
       [(«term_∨_»
         (SetTheory.Lists.«term_~_» `a " ~ " (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
         "∨"
         («term_∈_» `a "∈" `l₂))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_∨_»
       (SetTheory.Lists.«term_~_» `a " ~ " (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
       "∨"
       («term_∈_» `a "∈" `l₂))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `a "∈" `l₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l₂
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      (SetTheory.Lists.«term_~_» `a " ~ " (Term.anonymousCtor "⟨" [(Term.hole "_") "," `b] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
mutual
  @[ instance ]
      def
        Equiv.decidable
        [ DecidableEq α ] : ∀ l₁ l₂ : Lists α , Decidable l₁ ~ l₂
        |
            ⟨ ff , l₁ ⟩ , ⟨ ff , l₂ ⟩
            =>
            decidable_of_iff' l₁ = l₂ <| by cases l₁ <;> refine' equiv_atom.trans by simp [ atom ]
          | ⟨ ff , l₁ ⟩ , ⟨ tt , l₂ ⟩ => is_false <| by rintro ⟨ ⟩
          | ⟨ tt , l₁ ⟩ , ⟨ ff , l₂ ⟩ => is_false <| by rintro ⟨ ⟩
          |
            ⟨ tt , l₁ ⟩ , ⟨ tt , l₂ ⟩
            =>
            by
              haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
                            <
                            SizeOf.sizeOf ( ⟨ tt , l₁ ⟩ : Lists α )
                              +
                              SizeOf.sizeOf ( ⟨ tt , l₂ ⟩ : Lists α )
                        :=
                        by run_tac default_dec_tac
                      subset.decidable l₁ l₂
                haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf l₂ + SizeOf.sizeOf l₁
                            <
                            SizeOf.sizeOf ( ⟨ tt , l₁ ⟩ : Lists α )
                              +
                              SizeOf.sizeOf ( ⟨ tt , l₂ ⟩ : Lists α )
                        :=
                        by run_tac default_dec_tac
                      subset.decidable l₂ l₁
                exact decidable_of_iff' _ equiv.antisymm_iff
    @[ instance ]
      def
        Subset.decidable
        [ DecidableEq α ] : ∀ l₁ l₂ : Lists' α true , Decidable l₁ ⊆ l₂
        | Lists'.nil , l₂ => isTrue Subset.nil
          |
            @ Lists'.cons' _ b a l₁ , l₂
            =>
            by
              haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf ( ⟨ b , a ⟩ : Lists α ) + SizeOf.sizeOf l₂
                            <
                            SizeOf.sizeOf Lists'.cons' a l₁ + SizeOf.sizeOf l₂
                        :=
                        add_lt_add_right lt_sizeof_cons' _ _ _
                      mem.decidable ⟨ b , a ⟩ l₂
                haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf l₁ + SizeOf.sizeOf l₂
                            <
                            SizeOf.sizeOf Lists'.cons' a l₁ + SizeOf.sizeOf l₂
                        :=
                        by run_tac default_dec_tac
                      subset.decidable l₁ l₂
                exact decidable_of_iff' _ @ Lists'.cons_subset _ ⟨ _ , _ ⟩ _ _
    @[ instance ]
      def
        Mem.decidable
        [ DecidableEq α ] : ∀ ( a : Lists α ) ( l : Lists' α true ) , Decidable a ∈ l
        | a , Lists'.nil => is_false <| by rintro ⟨ _ , ⟨ ⟩ , _ ⟩
          |
            a , Lists'.cons' b l₂
            =>
            by
              haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf a + SizeOf.sizeOf ( ⟨ _ , b ⟩ : Lists α )
                            <
                            SizeOf.sizeOf a + SizeOf.sizeOf Lists'.cons' b l₂
                        :=
                        add_lt_add_left lt_sizeof_cons' _ _ _
                      equiv.decidable a ⟨ _ , b ⟩
                haveI
                  :=
                    have
                      :
                          SizeOf.sizeOf a + SizeOf.sizeOf l₂
                            <
                            SizeOf.sizeOf a + SizeOf.sizeOf Lists'.cons' b l₂
                        :=
                        by run_tac default_dec_tac
                      mem.decidable a l₂
                refine' decidable_of_iff' a ~ ⟨ _ , b ⟩ ∨ a ∈ l₂ _
                rw [ ← Lists'.mem_cons ]
                ;
                rfl
  end
  termination_by' ⟨ _ , measure_wf equiv.decidable_meas ⟩
#align lists.equiv.decidable Lists.Equiv.decidable
#align lists.subset.decidable Lists.Subset.decidable
#align lists.mem.decidable Lists.Mem.decidable

end Decidable

end Lists

namespace Lists'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_equiv_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`l] [":" (Term.app `Lists' [`α `true])] "}")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`a `a'] [] "}")]
         []
         ","
         (Term.arrow
          (SetTheory.Lists.«term_~_» `a " ~ " `a')
          "→"
          («term_↔_» («term_∈_» `a "∈" `l) "↔" («term_∈_» `a' "∈" `l))))))
      (Command.declValSimple
       ":="
       (Term.suffices
        "suffices"
        (Term.sufficesDecl
         []
         (Term.forall
          "∀"
          [(Term.implicitBinder "{" [`a `a'] [] "}")]
          []
          ","
          (Term.arrow
           (SetTheory.Lists.«term_~_» `a " ~ " `a')
           "→"
           (Term.arrow («term_∈_» `a "∈" `l) "→" («term_∈_» `a' "∈" `l))))
         (Term.fromTerm
          "from"
          (Term.fun
           "fun"
           (Term.basicFun
            [`a `a' `e]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `this [`e]) "," (Term.app `this [(Term.proj `e "." `symm)])]
             "⟩")))))
        []
        (Term.fun
         "fun"
         (Term.basicFun
          [`a₁ `a₂ `e₁ (Term.anonymousCtor "⟨" [`a₃ "," `m₃ "," `e₂] "⟩")]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            `m₃
            ","
            (Term.app (Term.proj (Term.proj `e₁ "." `symm) "." `trans) [`e₂])]
           "⟩"))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.suffices
       "suffices"
       (Term.sufficesDecl
        []
        (Term.forall
         "∀"
         [(Term.implicitBinder "{" [`a `a'] [] "}")]
         []
         ","
         (Term.arrow
          (SetTheory.Lists.«term_~_» `a " ~ " `a')
          "→"
          (Term.arrow («term_∈_» `a "∈" `l) "→" («term_∈_» `a' "∈" `l))))
        (Term.fromTerm
         "from"
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `a' `e]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `this [`e]) "," (Term.app `this [(Term.proj `e "." `symm)])]
            "⟩")))))
       []
       (Term.fun
        "fun"
        (Term.basicFun
         [`a₁ `a₂ `e₁ (Term.anonymousCtor "⟨" [`a₃ "," `m₃ "," `e₂] "⟩")]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.hole "_")
           ","
           `m₃
           ","
           (Term.app (Term.proj (Term.proj `e₁ "." `symm) "." `trans) [`e₂])]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a₁ `a₂ `e₁ (Term.anonymousCtor "⟨" [`a₃ "," `m₃ "," `e₂] "⟩")]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          `m₃
          ","
          (Term.app (Term.proj (Term.proj `e₁ "." `symm) "." `trans) [`e₂])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        `m₃
        ","
        (Term.app (Term.proj (Term.proj `e₁ "." `symm) "." `trans) [`e₂])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `e₁ "." `symm) "." `trans) [`e₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `e₁ "." `symm) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `e₁ "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`a₃ "," `m₃ "," `e₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `e₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `a' `e]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `this [`e]) "," (Term.app `this [(Term.proj `e "." `symm)])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `this [`e]) "," (Term.app `this [(Term.proj `e "." `symm)])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [(Term.proj `e "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `e "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [(Term.implicitBinder "{" [`a `a'] [] "}")]
       []
       ","
       (Term.arrow
        (SetTheory.Lists.«term_~_» `a " ~ " `a')
        "→"
        (Term.arrow («term_∈_» `a "∈" `l) "→" («term_∈_» `a' "∈" `l))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (SetTheory.Lists.«term_~_» `a " ~ " `a')
       "→"
       (Term.arrow («term_∈_» `a "∈" `l) "→" («term_∈_» `a' "∈" `l)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow («term_∈_» `a "∈" `l) "→" («term_∈_» `a' "∈" `l))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `a' "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_∈_» `a "∈" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (SetTheory.Lists.«term_~_» `a " ~ " `a')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SetTheory.Lists.«term_~_»', expected 'SetTheory.Lists.term_~_._@.SetTheory.Lists._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_equiv_left
  { l : Lists' α true } : ∀ { a a' } , a ~ a' → a ∈ l ↔ a' ∈ l
  :=
    suffices
      ∀ { a a' } , a ~ a' → a ∈ l → a' ∈ l from fun a a' e => ⟨ this e , this e . symm ⟩
      fun a₁ a₂ e₁ ⟨ a₃ , m₃ , e₂ ⟩ => ⟨ _ , m₃ , e₁ . symm . trans e₂ ⟩
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

