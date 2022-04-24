/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Lean
import Std.Data.HashMap

/-
A rudimentary export format, adapted from
<https://github.com/leanprover-community/lean/blob/master/doc/export_format.md>
with support for lean 4 kernel primitives.
-/
open Std (HashMap HashSet)

namespace Lean

namespace Export

/- References -/
private constant MethodsRefPointed : NonemptyType.{0}

private def MethodsRef : Type := MethodsRefPointed.type

inductive Entry
| name (n : Name)
| level (n : Level)
| expr (n : Expr)
| defn (n : Name)
deriving Inhabited

instance : Coe Name Entry := ⟨Entry.name⟩
instance : Coe Level Entry := ⟨Entry.level⟩
instance : Coe Expr Entry := ⟨Entry.expr⟩

structure Alloc (α) [BEq α] [Hashable α] where
  map : HashMap α Nat
  next : Nat
deriving Inhabited

structure State where
  names : Alloc Name := ⟨HashMap.empty.insert Name.anonymous 0, 1⟩
  levels : Alloc Level := ⟨HashMap.empty.insert levelZero 0, 1⟩
  exprs : Alloc Expr
  defs : HashSet Name
  stk : Array (Bool × Entry)
deriving Inhabited

class OfState (α : Type) [BEq α] [Hashable α] where
  get : State → Alloc α
  modify : (Alloc α → Alloc α) → State → State

instance : OfState Name where
  get s := s.names
  modify f s := { s with names := f s.names }

instance : OfState Level where
  get s := s.levels
  modify f s := { s with levels := f s.levels }

instance : OfState Expr where
  get s := s.exprs
  modify f s := { s with exprs := f s.exprs }

end Export

abbrev ExportM := StateT Export.State CoreM

namespace Export

def alloc {α} [BEq α] [Hashable α] [OfState α] (a : α) : ExportM Nat := do
  let n := (OfState.get (α := α) (← get)).next
  modify $ OfState.modify (α := α) fun s => {map := s.map.insert a n, next := n+1}
  pure n

def exportName (n : Name) : ExportM Nat := do
  match (← get).names.map.find? n with
  | some i => pure i
  | none => match n with
    | Name.anonymous => pure 0
    | Name.num p a _ => let i ← alloc n; IO.println s!"{i} #NI {← exportName p} {a}"; pure i
    | Name.str p s _ => let i ← alloc n; IO.println s!"{i} #NS {← exportName p} {s}"; pure i

def exportLevel (L : Level) : ExportM Nat := do
  match (← get).levels.map.find? L with
  | some i => pure i
  | none => match L with
    | Level.zero _ => pure 0
    | Level.succ l _ =>
      let i ← alloc L; IO.println s!"{i} #US {← exportLevel l}"; pure i
    | Level.max l₁ l₂ _ =>
      let i ← alloc L; IO.println s!"{i} #UM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | Level.imax l₁ l₂ _ =>
      let i ← alloc L; IO.println s!"{i} #UIM {← exportLevel l₁} {← exportLevel l₂}"; pure i
    | Level.param n _ =>
      let i ← alloc L; IO.println s!"{i} #UP {← exportName n}"; pure i
    | Level.mvar n _ => unreachable!

def biStr : BinderInfo → String
| BinderInfo.default        => "#BD"
| BinderInfo.implicit       => "#BI"
| BinderInfo.strictImplicit => "#BS"
| BinderInfo.instImplicit   => "#BC"
| BinderInfo.auxDecl        => unreachable!

open ConstantInfo in
mutual

partial def exportExpr (E : Expr) : ExportM Nat := do
  match (← get).exprs.map.find? E with
  | some i => pure i
  | none => match E with
    | Expr.bvar n _ => let i ← alloc E; IO.println s!"{i} #EV {n}"; pure i
    | Expr.fvar _ _ => unreachable!
    | Expr.mvar _ _ => unreachable!
    | Expr.sort l _ => let i ← alloc E; IO.println s!"{i} #ES {← exportLevel l}"; pure i
    | Expr.const n ls _ =>
      exportDef n
      let i ← alloc E
      let mut s := s!"{i} #EC {← exportName n}"
      for l in ls do s := s ++ s!" {← exportLevel l}"
      IO.println s; pure i
    | Expr.app e₁ e₂ _ =>
      let i ← alloc E; IO.println s!"{i} #EA {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | Expr.lam n e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EL {biStr d.binderInfo} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | Expr.forallE n e₁ e₂ d =>
      let i ← alloc E
      IO.println s!"{i} #EP {biStr d.binderInfo} {← exportExpr e₁} {← exportExpr e₂}"; pure i
    | Expr.letE n e₁ e₂ e₃ _ =>
      let i ← alloc E
      IO.println s!"{i} #EP {← exportExpr e₁} {← exportExpr e₂} {← exportExpr e₃}"; pure i
    | Expr.lit (Literal.natVal n) _ => let i ← alloc E; IO.println s!"{i} #EN {n}"; pure i
    | Expr.lit (Literal.strVal s) _ => let i ← alloc E; IO.println s!"{i} #ET {s}"; pure i
    | Expr.mdata _ e _ => unreachable!
    | Expr.proj n k e _ =>
      let i ← alloc E; IO.println s!"{i} #EJ {← exportName n} {k} {← exportExpr e}"; pure i

partial def exportDef (n : Name) : ExportM Unit := do
  if (← get).defs.contains n then return
  let ci ← getConstInfo n
  for c in ci.value!.getUsedConstants do
    unless (← get).defs.contains c do
      exportDef c
  match ci with
  | axiomInfo   val => axdef "#AX" val.name val.type val.levelParams
  | defnInfo    val => defn "#DEF" val.name val.type val.value val.levelParams
  | thmInfo     val => defn "#THM" val.name val.type val.value val.levelParams
  | opaqueInfo  val => defn "#CN" val.name val.type val.value val.levelParams
  | quotInfo    val =>
    IO.println "#QUOT"
    for n in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      insert n
  | inductInfo  val => ind val.all
  | ctorInfo    val => ind (← getConstInfoInduct val.induct).all
  | recInfo     val => ind val.all
where
  insert (n : Name) : ExportM Unit :=
    modify fun s => { s with defs := s.defs.insert n }
  defn (ty : String) (n : Name) (t e : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t} {← exportExpr e}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  axdef (ty : String) (n : Name) (t : Expr) (ls : List Name) : ExportM Unit := do
    let mut s := s!"{ty} {← exportName n} {← exportExpr t}"
    for l in ls do s := s ++ s!" {← exportName l}"
    IO.println s
    insert n
  ind : List Name → ExportM Unit
  | [] => unreachable!
  | is@(i::_) => do
    let val ← getConstInfoInduct i
    let mut s := match is.length with
    | 1 => s!"#IND {val.numParams}"
    | n => s!"#MUT {val.numParams} {n}"
    for j in is do insert j; insert (mkRecName j)
    for j in is do
      let vals ← getConstInfoInduct j
      s := s ++ s!" {← exportName val.name} {← exportExpr val.type} {val.ctors.length}"
      for c in val.ctors do
        insert c
        s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    for j in is do s ← indbody j s
    for l in val.levelParams do s := s ++ s!" {← exportName l}"
    IO.println s
  indbody (ind : Name) (s : String) : ExportM String := do
    let val ← getConstInfoInduct ind
    let mut s := s ++ s!" {← exportName ind} {← exportExpr val.type} {val.ctors.length}"
    for c in val.ctors do
      s := s ++ s!" {← exportName c} {← exportExpr (← getConstInfoCtor c).type}"
    pure s

end

def runExportM (m : ExportM α) : CoreM α := m.run' default

-- #eval runExportM (exportDef `Lean.Expr)
end Export

end Lean
