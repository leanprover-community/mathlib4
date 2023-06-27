/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbmap.basic
! leanprover-community/mathlib commit d13b3a4a392ea7273dfa4727dbd1892e26cfd518
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rbtree.Init

universe u v w

def RbmapLt {α : Type u} {β : Type v} (lt : α → α → Prop) (a b : α × β) : Prop :=
  lt a.1 b.1
#align rbmap_lt RbmapLt

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option auto_param.check_exists -/
set_option auto_param.check_exists false

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def Rbmap (α : Type u) (β : Type v)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Type max u v :=
  Rbtree (α × β) (RbmapLt lt)
#align rbmap Rbmap

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def mkRbmap (α : Type u) (β : Type v)
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt) :
    Rbmap α β lt :=
  mkRbtree (α × β) (RbmapLt lt)
#align mk_rbmap mkRbmap

namespace Rbmap

variable {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}

def empty (m : Rbmap α β lt) : Bool :=
  m.Empty
#align rbmap.empty Rbmap.empty

def toList (m : Rbmap α β lt) : List (α × β) :=
  m.toList
#align rbmap.to_list Rbmap.toList

def min (m : Rbmap α β lt) : Option (α × β) :=
  m.min
#align rbmap.min Rbmap.min

def max (m : Rbmap α β lt) : Option (α × β) :=
  m.max
#align rbmap.max Rbmap.max

def fold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.fold (fun e => f e.1 e.2) d
#align rbmap.fold Rbmap.fold

def revFold (f : α → β → δ → δ) (m : Rbmap α β lt) (d : δ) : δ :=
  m.revFold (fun e => f e.1 e.2) d
#align rbmap.rev_fold Rbmap.revFold

/-
We don't assume β is inhabited when in membership predicate `mem` and
function find_entry to make this module more convenient to use.
If we had assumed β to be inhabited we could use the following simpler
definition: (k, default) ∈ m
-/
protected def Mem (k : α) (m : Rbmap α β lt) : Prop :=
  match m.val with
  | Rbnode.leaf => False
  | Rbnode.red_node _ e _ => Rbtree.Mem (k, e.2) m
  | Rbnode.black_node _ e _ => Rbtree.Mem (k, e.2) m
#align rbmap.mem Rbmap.Mem

instance : Membership α (Rbmap α β lt) :=
  ⟨Rbmap.Mem⟩

instance [Repr α] [Repr β] : Repr (Rbmap α β lt) :=
  ⟨fun t => "rbmap_of " ++ repr t.toList⟩

def rbmapLtDec [h : DecidableRel lt] : DecidableRel (@RbmapLt α β lt) := fun a b => h a.1 b.1
#align rbmap.rbmap_lt_dec Rbmap.rbmapLtDec

variable [DecidableRel lt]

def insert (m : Rbmap α β lt) (k : α) (v : β) : Rbmap α β lt :=
  @Rbtree.insert _ _ rbmapLtDec m (k, v)
#align rbmap.insert Rbmap.insert

def findEntry (m : Rbmap α β lt) (k : α) : Option (α × β) :=
  match m.val with
  | Rbnode.leaf => none
  | Rbnode.red_node _ e _ => @Rbtree.find _ _ rbmapLtDec m (k, e.2)
  | Rbnode.black_node _ e _ => @Rbtree.find _ _ rbmapLtDec m (k, e.2)
#align rbmap.find_entry Rbmap.findEntry

def toValue : Option (α × β) → Option β
  | none => none
  | some e => some e.2
#align rbmap.to_value Rbmap.toValue

def find (m : Rbmap α β lt) (k : α) : Option β :=
  toValue (m.findEntry k)
#align rbmap.find Rbmap.find

def contains (m : Rbmap α β lt) (k : α) : Bool :=
  (findEntry m k).isSome
#align rbmap.contains Rbmap.contains

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def fromList (l : List (α × β))
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbmap α β lt :=
  l.foldl (fun m p => insert m p.1 p.2) (mkRbmap α β lt)
#align rbmap.from_list Rbmap.fromList

end Rbmap

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbtree.default_lt -/
def rbmapOf {α : Type u} {β : Type v} (l : List (α × β))
    (lt : α → α → Prop := by
      run_tac
        rbtree.default_lt)
    [DecidableRel lt] : Rbmap α β lt :=
  Rbmap.fromList l lt
#align rbmap_of rbmapOf

