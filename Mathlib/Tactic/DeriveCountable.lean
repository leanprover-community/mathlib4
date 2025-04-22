/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Batteries.Data.NameSet
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Nat.Pairing

/-!
# `Countable` deriving handler

Adds a deriving handler for the `Countable` class.
-/

namespace Mathlib.Deriving.Countable
open Lean Parser.Term Elab Deriving Meta

/-!
### Theory

We use the `Nat.pair` function to encode an inductive type in the natural numbers,
following a pattern similar to the tagged s-expressions used in Scheme/Lisp.
We develop a little theory to make constructing the injectivity functions very straightforward.

This is easiest to explain by example. Given a type
```lean
inductive T (α : Type)
  | a (n : α)
  | b (n m : α) (t : T α)
```
the deriving handler constructs the following three declarations:
```lean
noncomputable def T.toNat (α : Type) [Countable α] : T α → ℕ
  | a n => Nat.pair 0 (Nat.pair (encode n) 0)
  | b n m t => Nat.pair 1 (Nat.pair (encode n) (Nat.pair (encode m) (Nat.pair t.toNat 0)))

theorem T.toNat_injective (α : Type) [Countable α] : Function.Injective (T.toNat α) := fun
  | a .., a .. => by
    refine cons_eq_imp_init ?_
    refine pair_encode_step ?_; rintro ⟨⟩
    intro; rfl
  | a .., b .. => by refine cons_eq_imp ?_; rintro ⟨⟩
  | b .., a .. => by refine cons_eq_imp ?_; rintro ⟨⟩
  | b .., b .. => by
    refine cons_eq_imp_init ?_
    refine pair_encode_step ?_; rintro ⟨⟩
    refine pair_encode_step ?_; rintro ⟨⟩
    refine cons_eq_imp ?_; intro h; cases T.toNat_injective α h
    intro; rfl

instance (α : Type) [Countable α] : Countable (T α) := ⟨_, T.toNat_injective α⟩
```
-/

private noncomputable def encode {α : Sort*} [Countable α] : α → ℕ :=
  (Countable.exists_injective_nat α).choose

private noncomputable def encode_injective {α : Sort*} [Countable α] :
    Function.Injective (encode : α → ℕ) :=
  (Countable.exists_injective_nat α).choose_spec

/--
Initialize the injectivity argument. Pops the constructor tag.
-/
private theorem cons_eq_imp_init {p : Prop} {a b b' : ℕ}
    (h : b = b' → p) : Nat.pair a b = Nat.pair a b' → p := by
  simpa [Nat.pair_eq_pair, and_imp] using h

/--
Generic step of the injectivity argument, pops the head of the pairs.
Used in the recursive steps where we need to supply an additional injectivity argument.
-/
private theorem cons_eq_imp {p : Prop} {a b a' b' : ℕ}
    (h : a = a' → b = b' → p) : Nat.pair a b = Nat.pair a' b' → p := by
  rwa [Nat.pair_eq_pair, and_imp]

/--
Specialized step of the injectivity argument, pops the head of the pairs and decodes.
-/
private theorem pair_encode_step {p : Prop} {α : Sort*} [Countable α]
    {a b : α} {m n : ℕ}
    (h : a = b → m = n → p) : Nat.pair (encode a) m = Nat.pair (encode b) n → p :=
  cons_eq_imp fun ha => h (encode_injective ha)


/-!
### Implementation
-/

/-!
Constructing the `toNat` functions.
-/

private def mkToNatMatch (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal)
    (toFunNames : Array Name) : TermElabM Term := do
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
          let recName? := ctx.typeInfos.findIdx? (xTy.isAppOf ·.name) |>.map (toFunNames[·]!)
          rhsArgs := rhsArgs.push <| ←
            if let some recName := recName? then
              `($(mkIdent recName) $a)
            else
              ``(encode $a)
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let rhs' : Term ← rhsArgs.foldrM (init := ← `(0)) fun arg acc => ``(Nat.pair $arg $acc)
        let rhs : Term ← ``(Nat.pair $(quote ctorInfo.cidx) $rhs')
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
    return alts

/-- Constructs a function from the inductive type to `Nat`. -/
def mkToNatFuns (ctx : Deriving.Context) (toNatFnNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toNatFnNames.size] do
    let toNatFnName := toNatFnNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Countable 1 indVal
    let body ← mkToNatMatch ctx header indVal toNatFnNames
    res := res.push <| ← `(
      private noncomputable def $(mkIdent toNatFnName):ident $header.binders:bracketedBinder* :
        Nat := $body:term
      )
  `(command| mutual $[$res:command]* end)

/-!
Constructing the injectivity proofs for these `toNat` functions.
-/

private def mkInjThmMatch (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName₁ in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName₁
      for ctorName₂ in indVal.ctors do
        let mut patterns := #[]
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        patterns := patterns ++ #[(← `($(mkIdent ctorName₁) ..)), (← `($(mkIdent ctorName₂) ..))]
        if ctorName₁ == ctorName₂ then
          alts := alts.push <| ← forallTelescopeReducing ctorInfo.type fun xs _ => do
            let mut tactics : Array (TSyntax `tactic) := #[]
            for i in [:ctorInfo.numFields] do
              let x := xs[indVal.numParams + i]!
              let xTy ← inferType x
              let recName? :=
                ctx.typeInfos.findIdx? (xTy.isAppOf ·.name) |>.map (ctx.auxFunNames[·]!)
              tactics := tactics.push <| ←
                if let some recName := recName? then
                  `(tactic| (
                    refine $(mkCIdent ``cons_eq_imp) ?_;
                    intro h;
                    cases $(mkIdent recName) _ _ h
                  ))
                else
                  `(tactic| (
                    refine $(mkCIdent ``pair_encode_step) ?_;
                    rintro ⟨⟩
                  ))
            tactics := tactics.push (← `(tactic| (intro; rfl)))
            `(matchAltExpr| | $[$patterns:term],* => cons_eq_imp_init (by $tactics:tactic*))
        else if (← compatibleCtors ctorName₁ ctorName₂) then
          let rhs ← ``(cons_eq_imp (by rintro ⟨⟩))
          alts := alts.push (← `(matchAltExpr| | $[$patterns:term],* => $rhs:term))
    return alts

/-- Constructs a proof that the functions created by `mkToNatFuns` are injective. -/
def mkInjThms (ctx : Deriving.Context) (toNatFnNames : Array Name) :
    TermElabM (TSyntax `command) := do
  let mut res : Array (TSyntax `command) := #[]
  for i in [:toNatFnNames.size] do
    let toNatFnName := toNatFnNames[i]!
    let injThmName := ctx.auxFunNames[i]!
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeader ``Countable 2 indVal
    let body ← mkInjThmMatch ctx header indVal
    let f := mkIdent toNatFnName
    let t1 := mkIdent header.targetNames[0]!
    let t2 := mkIdent header.targetNames[1]!
    res := res.push <| ← `(
      private theorem $(mkIdent injThmName):ident $header.binders:bracketedBinder* :
        $f $t1 = $f $t2 → $t1 = $t2 := $body:term
      )
  `(command| mutual $[$res:command]* end)

/-!
Assembling the `Countable` instances.
-/

open TSyntax.Compat in
/-- Assuming all of the auxiliary definitions exist, create all the `instance` commands
for the `ToExpr` instances for the (mutual) inductive type(s). -/
private def mkCountableInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``Countable indVal argNames)
      let indType      ← mkInductiveApp indVal argNames
      let type         ← `($(mkCIdent ``Countable) $indType)
      let mut val      := mkIdent auxFunName
      let instCmd ← `(instance $binders:implicitBinder* : $type := ⟨_, $val⟩)
      instances := instances.push instCmd
  return instances

private def mkCountableCmds (indVal : InductiveVal) (declNames : Array Name) :
    TermElabM (Array Syntax) := do
  let ctx ← mkContext "countable" indVal.name
  let toNatFunNames : Array Name ← ctx.auxFunNames.mapM fun name => do
    let .str n' s := name.eraseMacroScopes | unreachable!
    mkFreshUserName <| .str n' (s ++ "ToNat")
  let cmds := #[← mkToNatFuns ctx toNatFunNames, ← mkInjThms ctx toNatFunNames]
    ++ (← mkCountableInstanceCmds ctx declNames)
  trace[Mathlib.Deriving.countable] "\n{cmds}"
  return cmds

open Command

/--
The deriving handler for the `Countable` class.
Handles non-nested non-reflexive inductive types.
They can be mutual too — in that case, there is an optimization to re-use all the generated
functions and proofs.
-/
def mkCountableInstance (declNames : Array Name) : CommandElabM Bool := do
  let mut seen : NameSet := {}
  let mut toVisit : Array InductiveVal := #[]
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isNested || indVal.isReflexive then
      return false -- not supported yet
    seen := seen.append (NameSet.ofList indVal.all)
    toVisit := toVisit.push indVal
  for indVal in toVisit do
    let cmds ← liftTermElabM <| mkCountableCmds indVal (declNames.filter indVal.all.contains)
    withEnableInfoTree false do
      elabCommand <| mkNullNode cmds
  return true

initialize
  registerDerivingHandler ``Countable mkCountableInstance
  registerTraceClass `Mathlib.Deriving.countable

end Mathlib.Deriving.Countable
