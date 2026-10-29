module

import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.InfoTree.Util

set_option linter.style.numericProjections true

open Lean

structure Foo where a : Nat
structure Bar extends Foo where b : Nat

variable (r : Rat) (bar : Bar)

def MySubtype := { a : Nat // a < 42 }

example (a : MySubtype) := a.1

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.den`.

To exempt terms of type `Rat`, add `@[allow_numeric_proj]` at the declaration site of `Rat`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs in
example := r.2

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs in
example := bar.2

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.toFoo`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
warning: Numeric projections are disallowed.

  [apply] Instead, use `.a`.

To exempt terms of type `Foo`, add `@[allow_numeric_proj]` at the declaration site of `Foo`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs in
example := bar.1.1

structure Fn where f : Nat → Nat

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.f`.

To exempt terms of type `Fn`, add `@[allow_numeric_proj]` at the declaration site of `Fn`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs in
example (g : Fn) := g.1 3

/-! The structure is the one the projection actually belongs to, found after unfolding. -/

def MyAnd (p q : Prop) : Prop := p ∧ q

#guard_msgs in
example (h : MyAnd True True) := h.2

/-! There is no named field to suggest for an `inductive` with one constructor. -/

inductive Ind | mk (x y : Nat)

#guard_msgs in
example (i : Ind) := i.2

open Elab Command in
/-- Elaborates `cmd`, then reports how many `TermInfo`s are numeric projections. The
`numericProjections` linter expects the `expr`s of all such infos to be constants (no metavariables
or metadata/annotations), so this ensures that this is indeed the case (and that we capture all the
projection infos we expect to).

If this output changes, consider following the advice in the body of `numericProjFn?` in the linter
and accounting for metavariables and annotations. -/
elab tk:"#numeric_proj_infos" " in " ppLine cmd:command : command => do
  elabCommand cmd
  let mut numInfos := 0
  let mut bad : Array MessageData := #[]
  for t in (← getInfoState).substituteLazy.get.trees do
    let numericProjInfos := t.foldInfo (init := #[]) fun _ info acc => match info with
      | .ofTermInfo i =>
        if i.stx.isOfKind Parser.Term.identProjKind && i.stx[0].isOfKind fieldIdxKind then
          acc.push i
        else acc
      | _ => acc
    numInfos := numInfos + numericProjInfos.size
    for i in numericProjInfos do
      unless i.expr.constName?.isSome do
        bad := bad.push m!"{i.stx}: {i.expr}"
  if bad.isEmpty then
    logInfoAt tk m!"Found {numInfos} numeric projection infos, all of which were `Expr.const`s"
  else
    logWarningAt tk m!"Found {numInfos} numeric projection infos, but some were not `Expr.const`s:\
      {indentD <| m!"\n".joinSep bad.toList}"

def MyBar := Bar
class C (α : Type) where c : α

/-! Term-mode elaboration paths: postponement, wrappers, `by` blocks, unfolding, classes,
notation, binders and structure instances. -/

/--
@ +1:0...19
info: Found 19 numeric projection infos, all of which were `Expr.const`s
---
@ +3:15...16
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +3:38...39
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +3:68...69
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:28...29
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:52...53
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:79...80
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:9...10
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:14...15
warning: Numeric projections are disallowed.

  [apply] Instead, use `.c`.

To exempt terms of type `C`, add `@[allow_numeric_proj]` at the declaration site of `C`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:24...25
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:39...40
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:59...60
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:6...7
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +6:25...26
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +6:45...46
warning: Numeric projections are disallowed.

  [apply] Instead, use `.toFoo`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +6:52...53
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +6:72...73
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +7:15...16
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +7:36...37
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +7:42...43
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs (positions := true, ordering := sorted) in
#numeric_proj_infos in
example (l : List Bar) (x : MyBar) [inst : C Nat] : List Nat × Prop := (
  [(fun y => y.2 : Bar → Nat) bar, (·.2 : Bar → Nat) bar, (l.map (·.2)).length,
    (bar.2 :), no_index bar.2, (by exact bar : Bar).2, (show Bar by exact bar).2,
    x.2, inst.1, if bar.2 = 0 then bar.2 else 1, match bar.2 with | 0 => 0 | n + 1 => n,
    ({ bar with b := bar.2 } : Bar).b, (⟨bar.1, bar.2⟩ : Bar).b, bar |>.2],
  ∀ y : Bar, y.2 = 0 ∧ ∃ z : Bar, z.2 = y.2)

/-! Tactic blocks, including a `first` alternative that fails. -/

/--
@ +2:0...19
info: Found 5 numeric projection infos, all of which were `Expr.const`s
---
@ +3:30...31
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:13...14
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:21...22
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:20...21
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:44...45
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs (positions := true, ordering := sorted) in
set_option linter.unusedTactic false in
#numeric_proj_infos in
example (h : bar.b = 2) : bar.2 = 2 := by
  have : bar.2 = bar.2 := rfl
  first | exact bar.2 | simp only [show bar.2 = 2 from h]

/-! Auxiliary definitions from `where` and `termination_by`. -/

/--
@ +1:0...19
info: Found 5 numeric projection infos, all of which were `Expr.const`s
---
@ +3:49...50
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +3:63...64
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +3:7...8
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +4:17...18
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
---
@ +5:27...28
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs (positions := true, ordering := sorted) in
#numeric_proj_infos in
def withAux (x : Bar) : Nat :=
  if x.2 = 0 then 0 else withAux { x with b := x.2 - 1 } + g x.2
termination_by x.2
where g (n : Nat) := n + x.2

/-! Inaccessible patterns are elaborated twice, leaving two infos but producing one warning. -/

/--
@ +1:0...19
info: Found 2 numeric projection infos, all of which were `Expr.const`s
---
@ +2:70...71
warning: Numeric projections are disallowed.

  [apply] Instead, use `.b`.

To exempt terms of type `Bar`, add `@[allow_numeric_proj]` at the declaration site of `Bar`.

Note: This linter can be disabled with `set_option linter.style.numericProjections false`
-/
#guard_msgs (positions := true, ordering := sorted) in
#numeric_proj_infos in
example (y : Foo) (h : y.a = bar.b) : Nat := match y, h with | ⟨.(bar.2)⟩, rfl => 0
