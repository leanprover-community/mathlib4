/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing

/-!
# `Encodable` deriving handler

Adds a deriving handler for the `Encodable` class.

The resulting `Encodable` instance should be considered to be opaque.
The specific encoding used is an implementation detail.
-/

namespace Mathlib.Deriving.Encodable
open Lean Parser.Term Elab Deriving Meta

/-!
### Theory

The idea is that every encodable inductive type can be represented as a tree of natural numbers.
Inspiration for this is s-expressions used in Lisp/Scheme.
```lean
inductive S : Type where
  | nat (n : ℕ)
  | cons (a b : S)
```
We start by constructing a equivalence `S ≃ ℕ` using the `Nat.pair` function.

Here is an example of how this module constructs an encoding.

Suppose we are given the following type:
```lean
inductive T (α : Type) where
  | a (x : α) (y : Bool) (z : T α)
  | b
```
The deriving handler constructs the following declarations:
```lean
def encodableT_toS {α} [Encodable α] (x : T α) : S :=
  match x with
  | T.a a a_1 a_2 =>
    S.cons (S.nat 0)
      (S.cons (S.nat (Encodable.encode a))
        (S.cons (S.nat (Encodable.encode a_1)) (S.cons (encodableT_toS a_2) (S.nat 0))))
  | T.b => S.cons (S.nat 1) (S.nat 0)

private def encodableT_fromS {α} [Encodable α] : S → Option (T α) := fun
  | S.cons (S.nat 0) (S.cons (S.nat a) (S.cons (S.nat a_1) (S.cons a_2 (S.nat 0)))) =>
    match Encodable.decode a, Encodable.decode a_1, encodableT_fromS a_2 with
    | some a, some a_1, some a_2 => some <| T.a a a_1 a_2
    | _, _, _ => none
  | S.cons (S.nat 1) (S.nat 0) => some <| T.b
  | _ => none

private theorem encodableT {α} [Encodable α] (x : @T α) :
    encodableT_fromS (encodableT_toS x) = some x := by
  cases x <;> (unfold encodableT_toS encodableT_fromS; simp only [Encodable.encodek, encodableT])

instance {α} [Encodable α] : Encodable (@T α) :=
  Encodable.ofLeftInjection encodableT_toS encodableT_fromS encodableT
```
The idea is that each constructor gets encoded as a linked list made of `S.cons` constructors
that is tagged with the constructor index.
-/

private inductive S : Type where
  | nat (n : ℕ)
  | cons (a b : S)

private def S.encode : S → ℕ
  | nat n => Nat.pair 0 n
  | cons a b => Nat.pair (S.encode a + 1) (S.encode b)

private lemma nat_unpair_lt_2 {n : ℕ} (h : (Nat.unpair n).1 ≠ 0) : (Nat.unpair n).2 < n := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have := Nat.le_mul_self a
  have := Nat.le_mul_self b
  split <;> omega

private def S.decode (n : ℕ) : S :=
  let p := Nat.unpair n
  if h : p.1 = 0 then
    S.nat p.2
  else
    have : p.1 ≤ n := Nat.unpair_left_le n
    have := Nat.unpair_lt (by cutsat : 1 ≤ n)
    have := nat_unpair_lt_2 h
    S.cons (S.decode (p.1 - 1)) (S.decode p.2)

private def S_equiv : S ≃ ℕ where
  toFun := S.encode
  invFun := S.decode
  left_inv s := by
    induction s with
    | nat n =>
      unfold S.encode S.decode
      simp
    | cons a b iha ihb =>
      unfold S.encode S.decode
      simp [iha, ihb]
  right_inv n := by -- The fact it's a right inverse isn't needed for the deriving handler.
    induction n using Nat.strongRecOn with | _ n ih =>
    unfold S.decode
    dsimp only
    split
    next h =>
      unfold S.encode
      rw [← h, Nat.pair_unpair]
    next h =>
      unfold S.encode
      rw [ih, ih, Nat.sub_add_cancel, Nat.pair_unpair]
      · rwa [Nat.one_le_iff_ne_zero]
      · exact nat_unpair_lt_2 h
      · obtain _ | n' := n
        · exact False.elim (h rfl)
        · have := Nat.unpair_lt (by omega : 1 ≤ n' + 1)
          omega

instance : Encodable S := Encodable.ofEquiv ℕ S_equiv

/-!
### Implementation
-/

/-!
Constructing the `toS` encoding functions.
-/

private def mkToSMatch (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal)
    (toSNames : Array Name) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      alts := alts.push <| ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        let mut ctorArgs := #[]
        let mut rhsArgs : Array Term := #[]
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        for _ in [:ctorInfo.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          let x := xs[ctorInfo.numParams + i]!
          let xTy ← inferType x
          let recName? := ctx.typeInfos.findIdx? (xTy.isAppOf ·.name) |>.map (toSNames[·]!)
          rhsArgs := rhsArgs.push <| ←
            if let some recName := recName? then
              `($(mkIdent recName) $a)
            else
              ``(S.nat (Encodable.encode $a))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let rhs' : Term ← rhsArgs.foldrM (init := ← ``(S.nat 0)) fun arg acc => ``(S.cons $arg $acc)
        let rhs : Term ← ``(S.cons (S.nat $(quote ctorInfo.cidx)) $rhs')
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
    return alts

/-- Constructs a function from the inductive type to `S`. -/
private def mkToSFuns (ctx : Deriving.Context) (toSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toNatFnName := toSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkToSMatch ctx header indVal toSFunNames
    res := res.push <| ← `(
      private def $(mkIdent toNatFnName):ident $header.binders:bracketedBinder* :
        $(mkCIdent ``S) := $body:term
      )
  `(command| mutual $[$res:command]* end)

/-!
Constructing the `fromS` functions.
-/

private def mkFromSMatch (ctx : Deriving.Context) (indVal : InductiveVal)
    (fromSNames : Array Name) : TermElabM Term := do
  let alts ← mkAlts
  `(fun $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      alts := alts.push <| ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patternArgs : Array Term := #[]
        let mut discrs : Array (TSyntax ``Lean.Parser.Term.matchDiscr) := #[]
        let mut ctorArgs : Array Term := #[]
        let mut patternArgs2 : Array Term := #[]
        let mut patternArgs3 : Array Term := #[]
        for _ in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          let x := xs[ctorInfo.numParams + i]!
          let xTy ← inferType x
          let recName? := ctx.typeInfos.findIdx? (xTy.isAppOf ·.name) |>.map (fromSNames[·]!)
          if let some recName := recName? then
            patternArgs := patternArgs.push a
            discrs := discrs.push <| ← `(matchDiscr| $(mkIdent recName) $a)
          else
            patternArgs := patternArgs.push <| ← ``(S.nat $a)
            discrs := discrs.push <| ← `(matchDiscr| $(mkCIdent ``Encodable.decode) $a)
          ctorArgs := ctorArgs.push a
          patternArgs2 := patternArgs2.push <| ← ``(some $a)
          patternArgs3 := patternArgs3.push <| ← `(_)
        let pattern ← patternArgs.foldrM (init := ← ``(S.nat 0)) fun arg acc => ``(S.cons $arg $acc)
        let pattern ← ``(S.cons (S.nat $(quote ctorInfo.cidx)) $pattern)
        -- Note: this is where we could try to handle indexed types.
        -- The idea would be to use DecidableEq to test the computed index against the expected
        -- index and then rewrite.
        let res ← ``(some <| @$(mkIdent ctorName):ident $ctorArgs:term*)
        if discrs.isEmpty then
          `(matchAltExpr| | $pattern:term => $res)
        else
          let rhs : Term ← `(
              match $[$discrs],* with
              | $[$patternArgs2],* => $res
              | $[$patternArgs3],* => none
            )
          `(matchAltExpr| | $pattern:term => $rhs)
    alts := alts.push <| ← `(matchAltExpr| | _ => none)
    return alts

/-- Constructs a function from `S` to the inductive type. -/
private def mkFromSFuns (ctx : Deriving.Context) (fromSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:fromSFunNames.size] do
    let fromNatFnName := fromSFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let body ← mkFromSMatch ctx indVal fromSFunNames
    -- Last binder is for the target
    let binders := header.binders[0:header.binders.size - 1]
    res := res.push <| ← `(
      private def $(mkIdent fromNatFnName):ident $binders:bracketedBinder* :
        $(mkCIdent ``S) → Option $header.targetType := $body:term
      )
  `(command| mutual $[$res:command]* end)

/-!
Constructing the proofs that the `fromS` functions are left inverses of the `toS` functions.
-/

/--
Constructs a proof that the functions created by `mkFromSFuns` are left inverses
of the ones created by `mkToSFuns`.
-/
private def mkInjThms (ctx : Deriving.Context) (toSFunNames fromSFunNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toSFunNames.size] do
    let toSFunName := toSFunNames[i]!
    let fromSFunName := fromSFunNames[i]!
    let injThmName := ctx.auxFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Encodable 1 indVal
    let enc := mkIdent toSFunName
    let dec := mkIdent fromSFunName
    let t := mkIdent header.targetNames[0]!
    let lemmas : TSyntaxArray ``Parser.Tactic.simpLemma ← ctx.auxFunNames.mapM fun i =>
      `(Parser.Tactic.simpLemma| $(mkIdent i):term)
    let tactic : Term ← `(by
        cases $t:ident
        <;> (unfold $(mkIdent toSFunName):ident $(mkIdent fromSFunName):ident;
              simp only [Encodable.encodek, $lemmas,*]; try rfl)
      )
    res := res.push <| ← `(
      private theorem $(mkIdent injThmName):ident $header.binders:bracketedBinder* :
        $dec ($enc $t) = some $t := $tactic
      )
  `(command| mutual $[$res:command]* end)

/-!
Assembling the `Encodable` instances.
-/

open TSyntax.Compat in
/-- Assuming all of the auxiliary definitions exist, create all the `instance` commands
for the `ToExpr` instances for the (mutual) inductive type(s). -/
private def mkEncodableInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name)
    (toSFunNames fromSFunNames : Array Name) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``Encodable indVal argNames)
      let indType      ← mkInductiveApp indVal argNames
      let type         ← `($(mkCIdent ``Encodable) $indType)
      let encode       := mkIdent toSFunNames[i]!
      let decode       := mkIdent fromSFunNames[i]!
      let kencode      := mkIdent auxFunName
      let instCmd ← `(
        instance $binders:implicitBinder* : $type :=
          $(mkCIdent ``Encodable.ofLeftInjection) $encode $decode $kencode
        )
      instances := instances.push instCmd
  return instances

private def mkEncodableCmds (indVal : InductiveVal) (declNames : Array Name) :
    TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Encodable "encodable" indVal.name
  let toSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
    mkFreshUserName <| .str n' (s ++ "_toS")
  let fromSFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
    mkFreshUserName <| .str n' (s ++ "_fromS")
  let cmds :=
    #[← mkToSFuns ctx toSFunNames,
      ← mkFromSFuns ctx fromSFunNames,
      ← mkInjThms ctx toSFunNames fromSFunNames]
    ++ (← mkEncodableInstanceCmds ctx declNames toSFunNames fromSFunNames)
  trace[Mathlib.Deriving.encodable] "\n{cmds}"
  return cmds

open Command

/--
The deriving handler for the `Encodable` class.
Handles non-nested non-reflexive inductive types.
They can be mutual too — in that case, there is an optimization to re-use all the generated
functions and proofs.
-/
def mkEncodableInstance (declNames : Array Name) : CommandElabM Bool := do
  let mut seen : NameSet := {}
  let mut toVisit : Array InductiveVal := #[]
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isNested || indVal.isReflexive || indVal.numIndices != 0 then
      return false -- not supported yet
    seen := seen.append (NameSet.ofList indVal.all)
    toVisit := toVisit.push indVal
  for indVal in toVisit do
    let cmds ← liftTermElabM <| mkEncodableCmds indVal (declNames.filter indVal.all.contains)
    withEnableInfoTree false do
      elabCommand <| mkNullNode cmds
  return true

initialize
  registerDerivingHandler ``Encodable mkEncodableInstance
  registerTraceClass `Mathlib.Deriving.Encodable

end Mathlib.Deriving.Encodable
