/-
Copyright (c) 2023 Vladimir Sedlacek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Sedlacek
-/
import Mathlib.Geometry.Synthetic.Avigad.Axioms

/-!
Tactics document for permutation of arguments
-/

open IncidenceGeometry

variable [i: IncidenceGeometry] {a b c : Point}

theorem area_invariant a b c : area a b c = area c a b ∧ area a b c = area a c b :=
  ⟨area_invariant_cycle a b c, area_invariant_flip a b c⟩

lemma ar132  : area a b c = area a c b := by exact (area_invariant a b c).2

lemma ar312  : area a b c = area c a b := by exact (area_invariant a b c).1

lemma ar231  : area a b c = area b c a :=
  by rw [(area_invariant a b c).1]; rw [(area_invariant c a b).1]

lemma ar213  : area a b c = area b a c :=
  by rw [(area_invariant a b c).2]; rw [(area_invariant a c b).1]

lemma ar321  : area a b c = area c b a :=
  by rw [(area_invariant a b c).2]; rw [(area_invariant c b a).1]

lemma col213  : colinear a b c ↔ colinear b a c := by
  constructor
  all_goals
    intro h
    obtain ⟨ L, hL ⟩ := h
    use L
    exact and_left_comm.mp hL

lemma col231 : colinear a b c ↔ colinear b c a := by
  constructor
  all_goals
    intro h
    obtain ⟨ L, hL ⟩ := h
    use L
  exact and_rotate.mp hL
  exact and_rotate.mpr hL

lemma col132 : colinear a b c ↔ colinear a c b := by conv => rhs; rw [col213]; rw [col231]

lemma col312 : colinear a b c ↔ colinear c a b := by conv => lhs; rw [← col231]

lemma col321 : colinear a b c ↔ colinear c b a := by conv => rhs; rw [col231]; rw [col213]

lemma tr132  : triangle a b c ↔ triangle a c b := by
  constructor; all_goals dsimp [triangle]; rw [col132]; tauto

lemma tr213  : triangle a b c ↔ triangle b a c := by
  constructor; all_goals dsimp [triangle]; rw [col213]; tauto

lemma tr231  : triangle a b c ↔ triangle b c a := by
  constructor; all_goals dsimp [triangle]
  rw [col231]; tauto
  rw [← col231]; tauto

lemma tr312  : triangle a b c ↔ triangle c a b := by
  constructor; all_goals dsimp [triangle]
  rw [col312]; tauto
  rw [← col312]; tauto

lemma tr321  : triangle a b c ↔ triangle c b a := by
  constructor; all_goals dsimp [triangle]; rw [col321]; tauto

lemma ss21 {a b : Point} {L : Line}: SameSide a b L ↔ SameSide b a L := by
  constructor; repeat exact sameside_symm

lemma ds21 {a b : Point} {L : Line}: diffside a b L ↔ diffside b a L := by
  constructor
  all_goals
    intro h
    obtain ⟨ naL, nbL, nss ⟩ := h
    rw [ss21] at nss
    exact ⟨ nbL, naL, nss ⟩

lemma para21 {L M : Line}: para L M ↔ para M L := by
  constructor
  all_goals
    intros p e
    rw [Or.comm]
    exact p e

namespace Lean.Elab.Tactic

/-- Definitions for perm tactic-/
def getNthArgName (tgt : Expr) (n : Nat) : MetaM Name :=
  do
    let some id := Lean.Expr.fvarId? (Lean.Expr.getArg! tgt n) | throwError
      "argument {n} is not a free variable"
    id.getUserName

/-- Definitions for perm tactic-/
def lte (n1 : @& Name) (n2: @& Name) : Bool :=
  Name.lt n1 n2 || n1 = n2

/-- ## Conv tactic `area_nf`
A conv tactic for permuting the variables in an `area` expression. A building block for the `perm`
tactic.
 -/
elab "area_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@ar132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@ar213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@ar312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@ar231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@ar321 _ _ _] )) -- cba

/-- ## Conv tactic `colinear_nf`
A conv tactic for permuting the variables in an `colinear` expression. A building block for the
`perm` tactic.
 -/
elab "colinear_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@col132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@col213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@col312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@col231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@col321 _ _ _] )) -- cba

/-- ## Conv tactic `triangle_nf`
A conv tactic for permuting the variables in an `triangle` expression. A building block for the
`perm` tactic.
 -/
elab "triangle_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@tr132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@tr213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@tr312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@tr231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@tr321 _ _ _] )) -- cba

/-- ## Conv tactic `length_nf`
A conv tactic for permuting the variables in an `length` expression. A building block for the
`perm` tactic.
 -/
elab "length_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@length_symm _ _] ))

/-- ## Conv tactic `angle_nf`
A conv tactic for permuting the variables in an `angle` expression. A building block for the
`perm` tactic.
 -/
elab "angle_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n3 ← getNthArgName tgt 3
  if n3.lt n1 then
    evalTactic (← `(tactic| rw [@angle_symm _ _] ))

/-- ## Conv tactic `sameside_nf`
A conv tactic for permuting the variables in an `sameside` expression. A building block for the
`perm` tactic.
 -/
elab "sameside_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@ss21 _ _] ))

/-- ## Conv tactic `diffside_nf`
A conv tactic for permuting the variables in an `diffside` expression. A building block for the
`perm` tactic.
 -/
elab "diffside_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@ds21 _ _] ))

/-- ## Conv tactic `para_nf`
A conv tactic for permuting the variables in an `para` expression. A building block for the `perm`
tactic.
 -/
elab "para_nf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@para21 _ _] ))

/-- ## Tactic perm
A custom experimental tactic for permuting the variables in geometric primitives. The ordering is
the one in which the variables are introduced, so it is not necessarily lexigraphic in general.
Usage:
- `perm` permutes the variables in the goal
- `perm at h1, h2, ...` permutes the variables in hypotheses `h1`, `h2`, ...
- `perm at *` permutes the variables in the goal and all hypotheses
- `perm [t1 t2 ...]` adds permuted proof terms `t1, t2, ...` to the local context, then runs `perm`
In each of these variants but the last, `perm` can be replaced with `perm only [perm_type]`, where
`perm_type` is one of area, colinear, triangle, length, angle, sameside, diffside.
 -/
syntax "perm" (" [" term,* "]")? ("only [" ident "]")? ("at " ident,* )? ("at *")? : tactic
macro_rules
  | `(tactic| perm) => `(tactic|
    (
      try conv in (occs := *) area _ _ _ => all_goals area_nf
      try conv in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try conv in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try conv in (occs := *) length _ _ => all_goals length_nf
      try conv in (occs := *) angle _ _ _ => all_goals angle_nf
      try conv in (occs := *) SameSide _ _ _ => all_goals sameside_nf
      try conv in (occs := *) diffside _ _ _ => all_goals diffside_nf
      try conv in (occs := *) para _ _ => all_goals para_nf
    ))
  | `(tactic| perm at $h) => `(tactic|
    (
      try conv at $h in (occs := *) area _ _ _ => all_goals area_nf
      try conv at $h in (occs := *) colinear _ _ _ => all_goals colinear_nf
      try conv at $h in (occs := *) triangle _ _ _ => all_goals triangle_nf
      try conv at $h in (occs := *) length _ _ => all_goals length_nf
      try conv at $h in (occs := *) angle _ _ _ => all_goals angle_nf
      try conv at $h in (occs := *) SameSide _ _ _ => all_goals sameside_nf
      try conv at $h in (occs := *) diffside _ _ _ => all_goals diffside_nf
      try conv at $h in (occs := *) para _ _ => all_goals para_nf
    ))
  | `(tactic| perm at $h:ident, $hs:ident,*) => `(tactic| perm at $h; perm at $hs,*)

open Lean Meta in
/-- Definitions for perm tactic-/
def haveExpr (n : Name) (h : Expr) :=
  withMainContext do
    let t ← inferType h
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← Lean.MVarId.assert mvarId n t h
      let (_, mvarIdNew) ← Lean.MVarId.intro1P mvarIdNew
      return [mvarIdNew]

open Parser Tactic Syntax

/-- Definitions for perm tactic-/
syntax "havePerms" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| havePerms $[[$args,*]]?) => withMainContext do
    let hyps := (← ((args.map (TSepArray.getElems)).getD {}).mapM (elabTerm ·.raw none)).toList
    for h in hyps do
      haveExpr "this" h
      evalTactic (← `(tactic| perm at $(mkIdent "this")))

macro_rules
  | `(tactic| perm [$args,*] ) => `(tactic| havePerms [$args,*]; perm)

elab_rules: tactic
  | `(tactic| perm only [$perm_type:ident]) => do
    if perm_type == mkIdent `area then
        evalTactic (← `(tactic| try conv in (occs := *) area _ _ _ => all_goals area_nf))
    else if perm_type == mkIdent `colinear then
      evalTactic (← `(tactic| try conv in (occs := *) colinear _ _ _ => all_goals colinear_nf))
    else if perm_type == mkIdent `triangle then
      evalTactic (← `(tactic| try conv in (occs := *) triangle _ _ _ => all_goals triangle_nf))
    else if perm_type == mkIdent `length then
      evalTactic (← `(tactic| try conv in (occs := *) length _ _ => all_goals length_nf))
    else if perm_type == mkIdent `angle then
      evalTactic (← `(tactic| try conv in (occs := *) angle _ _ _ => all_goals angle_nf))
    else if perm_type == mkIdent `SameSide then
      evalTactic (← `(tactic| try conv in (occs := *) SameSide _ _ _ => all_goals sameside_nf))
    else if perm_type == mkIdent `diffside then
      evalTactic (← `(tactic| try conv in (occs := *) diffside _ _ _ => all_goals diffside_nf))
    else if perm_type == mkIdent `para then
      evalTactic (← `(tactic| try conv in (occs := *) para _ _ => all_goals para_nf))
    else
      throwError "permutation type {perm_type} is not valid, please use one of
        'area/colinear/triangle/length/angle/sameside/diffside/para'"
  | `(tactic| perm only [$perm_type:ident] at $h:ident) => withMainContext do
    if perm_type == mkIdent `area then
      evalTactic (← `(tactic| try conv at $h in (occs := *) area _ _ _ => all_goals area_nf))
    else if perm_type == mkIdent `colinear then
      evalTactic (← `(tactic| try conv at $h in (occs := *) colinear _ _ _
        => all_goals colinear_nf))
    else if perm_type == mkIdent `triangle then
      evalTactic (← `(tactic| try conv at $h in (occs := *) triangle _ _ _
        => all_goals triangle_nf))
    else if perm_type == mkIdent `length then
      evalTactic (← `(tactic| try conv at $h in (occs := *) length _ _ => all_goals length_nf))
    else if perm_type == mkIdent `angle then
      evalTactic (← `(tactic| try conv at $h in (occs := *) angle _ _ _ => all_goals angle_nf))
    else if perm_type == mkIdent `SameSide then
      evalTactic (← `(tactic| try conv at $h in (occs := *) SameSide _ _ _
        => all_goals sameside_nf))
    else if perm_type == mkIdent `diffside then
      evalTactic (← `(tactic| try conv at $h in (occs := *) diffside _ _ _
        => all_goals diffside_nf))
    else if perm_type == mkIdent `para then
      evalTactic (← `(tactic| try conv at $h in (occs := *) para _ _ => all_goals para_nf))
    else
      throwError "permutation type {perm_type} is not valid, please use one of
        'area/colinear/triangle/length/angle/sameside/diffside'"
  | `(tactic| perm at *) => withMainContext do
    evalTactic (← `(tactic| perm))
    for ldecl in ← getLCtx do
      let name := mkIdent ldecl.userName
      if !ldecl.isImplementationDetail then evalTactic (← `(tactic| perm at $name))
  | `(tactic| perm only [$perm_type] at *) => withMainContext do
    evalTactic (← `(tactic| perm only [$perm_type]))
    for ldecl in ← getLCtx do
      let name := mkIdent ldecl.userName
      if !ldecl.isImplementationDetail then evalTactic (← `(tactic| perm only [$perm_type] at
        $name))

/-- Definitions for perm tactic-/
elab "assumption_symm" : tactic => withMainContext do
  for ldecl in ← getLCtx do
    let name := mkIdent ldecl.userName
    if !ldecl.isImplementationDetail then
      evalTactic (← `(tactic| try exact Eq.symm $name))

/-- ## Tactic perma
Like `perm`, but also tries to exact assumptions and their symmetrized versions.
 -/
syntax "perma" ("[" term,* "]")? ("only [" ident "]")? ("at " ident,* )? ("at *")? : tactic

macro_rules
  | `(tactic| perma) => `(tactic| perm; try assumption; try assumption_symm)
  | `(tactic| perma at $h) => `(tactic| perm at $h; try exact $h; try exact Eq.symm $h)
  | `(tactic| perma at $h:ident, $hs:ident,*) => `(tactic| perma at $h; perma at $hs,*)
  | `(tactic| perma only [$perm_type]) =>
      `(tactic| perm only [$perm_type]; try assumption; try assumption_symm)
  | `(tactic| perma only [$perm_type] at $h) =>
      `(tactic| perm only [$perm_type] at $h:ident; try exact $h; try exact Eq.symm $h)
  | `(tactic| perma at *) =>
      `(tactic| perm at *; try assumption; try assumption_symm)
  | `(tactic| perma only [$perm_type] at *) =>
      `(tactic| perm only [$perm_type] at *; try assumption; try assumption_symm)
  | `(tactic| perma [$args,*] ) =>
      `(tactic| perm [$args,*]; try assumption; try assumption_symm)

/-- ## Tactic linperm
A combination of linarith and perm.
Usage:
- `linperm` runs `perm at *` followed by `linarith`
- `linperm [t1 t2 ...]` runs `perm at *`, adds permuted proof terms `t1, t2, ...` to the local
context, and finishes with `linarith`
 -/
syntax "linperm " ("[" term,* "]")? : tactic

macro_rules
  | `(tactic| linperm) => `(tactic| perm at *; linarith)
  | `(tactic| linperm [$args,*] ) => `(tactic| perm at *; havePerms [$args,*]; linarith)


/-- Tactic for breaking ands up-/
macro "splitAll" : tactic => `(tactic | repeat' constructor)

/-- by_contra followed push_neg-/
syntax "push_contra" binderIdent location: tactic

macro_rules
  | `(tactic| push_contra $h:binderIdent $l:location) => `(tactic|
    (
      by_contra $h
      push_neg $l
    ))
