import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Defs
import Mathlib.adomaniLeanUtils.inspect_syntax
import Batteries.Data.Array.Basic
import Mathlib.Tactic

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

partial
def filterMapM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option Syntax)) :
    m (Array Syntax) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap (stx : Syntax) (f : Syntax → Option Syntax) : Array Syntax :=
  stx.filterMapM (m := Id) f

def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

open Lean Elab Command

/-- the `SyntaxNodeKind`s of `intro` and `intros`. -/
abbrev introTacs := #[``Lean.Parser.Tactic.intros, ``Lean.Parser.Tactic.intro]

open Lean.Parser.Tactic in
/-- if the input is `have .. : ∀ ids : typs, ... := by intro(s)...`, then
it returns `(#[ids, typs], #[intro(s)])`, otherwise it returns `(#[], #[])`.
Note that `typs` could be `null`.
-/
def getVarsAndInfos : Syntax → (Array Syntax × Array Syntax)
  | .node _ ``Lean.Parser.Term.haveIdDecl #[
      _, -- have id
      _, -- new binders as in `have test {x : Nat}`
      ts?,
      _, -- `:=`
      intro? -- actual proof
    ] =>
      let vars := match ts? with
        | .node s1 k1 #[
            .node s2 ``Lean.Parser.Term.typeSpec #[
              colon,
              .node _ ``Lean.Parser.Term.forall #[
                _, -- `∀`
                ids, -- identifiers
                ts, -- `typeSpec`
                _, -- comma `,`
                body  -- body of `∀`
              ]
            ]
          ] =>
          dbg_trace "{Syntax.node s1 k1 #[.node s2 ``Lean.Parser.Term.typeSpec #[colon, body]]}"
          dbg_trace "{Syntax.node s1 k1 #[.node s2 ``Lean.Parser.Term.typeSpec #[colon, body]]}"
          #[ids, ts]
        | _ => #[]
      let intros? := match intro? with
        | .node _ _ #[_, -- `by`
            .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ _ args]]] =>
          let firstTac := args[0]!
          if introTacs.contains firstTac.getKind then
            #[firstTac]
          else #[]
        | _ => #[]
      (vars, intros?)
  | _ => default
--#eval do ← `(tactic| have : $ := $)
inspect
example : True := by
  have (test : Nat) : test = test := by rfl
  trivial
#check Lean.Parser.Term.letIdBinder

def recombineBinders
    (haveIds : TSyntaxArray `Lean.Parser.Term.letIdBinder)
    (foralls : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder])
    (body value : TSyntax `term) :
    TSyntaxArray `Lean.Parser.Term.letIdBinder ×
    TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] ×
    TSyntax `term ×
    TSyntax `term :=
  -- I decided that to test this, I was going to move every entry of `foralls` to `haveIds`
  -- one at a time.  We will have to only move them as long as it makes sense, coordinating
  -- with the `intros` as well: this is just a test
  let first := foralls.getD 0 default
  --dbg_trace first
  (haveIds.push ⟨first.raw⟩, foralls.erase first, body, value)

def allStxCore : Syntax → CommandElabM (Option Syntax)
  | `(tactic| have $id:haveId $bi1* : ∀ $bi2*, $body := $t) => do
    dbg_trace "bi1: '{bi1}'\nbi2: '{bi2}'\n"
    let (bi1', bi2', body', t') := recombineBinders bi1 bi2 body t
    --let ident := mkIdent `hyp
    let new := ←
      if bi2'.isEmpty then `(tactic| have $id:haveId $[$bi1']* : $body' := $t')
      else `(tactic| have $id:haveId $[$bi1']* : ∀ $[$bi2']*, $body' := $t')
    return some new
  | _ => return none

partial
def allStx (stx : Syntax) : CommandElabM Syntax := do
  match ← allStxCore stx with
    | none => return stx
    | some stx => allStx stx

elab "fh " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter (·.isOfKind ``Lean.Parser.Tactic.tacticHave_)
  for stx in haves do
--  if let some stx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    dbg_trace "found have"
    let newHave ← allStx stx
    --logInfo newHave
    let newCmd ← cmd.raw.replaceM fun s => do if s == stx then return some newHave else return none
    logInfo newCmd
    -- to make sure that we are not only producing correct `Syntax`, but actually working code,
    -- I tried elaborating the command obtained by replacing each `have` separately with its
    -- new form
    elabCommand newCmd
    logInfo "elaborated!"

-- and the test is successful!
fh
--inspect
example : True := by
  have (_ : Nat) x y : x + y = 0 := by intros; sorry
  have (_ : Nat) : ∀ x y, x + y = 0 := by intros; sorry --rfl
  trivial

fh
--inspect
example : True := by
  have (_ : Nat) : ∀ _, ‹_› = 0 := by
    intros
    sorry --rfl
  trivial

example : True :=
  by
  have (_ : Nat) _ : ‹_› = 0 := by
    intros
    sorry
      --rfl
  trivial


#exit
inspect
example : True := by
  have : ∀ (test : Nat), test = test := by intros b; rfl
  trivial







/-- returns true iff the input is of the form `have .. : ∀ ids : typs, ... := by intro(s)...`. -/
def findForall (stx : Syntax) : Bool :=
  let (a, b) := getVarsAndInfos stx
  !(a.isEmpty || b.isEmpty)
/-
|-node Lean.Parser.Term.byTactic, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'by'
|   |-node Lean.Parser.Tactic.tacticSeq, none
|   |   |-node Lean.Parser.Tactic.tacticSeq1Indented, none
|   |   |   |-node null, none
|   |   |   |   |-node Lean.Parser.Tactic.intros, none
|   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- 'intros'
|   |   |   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ';'
|   |   |   |   |-node Lean.Parser.Tactic.exact, none
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- 'exact'
|   |   |   |   |   |-node num, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- '0'

-/


/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
-- ts?
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node Lean.Parser.Term.forall, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '∀'
|   |   |   |   |-node null, none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |   |   |-node null, none
|   |   |   |   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ','
|   |   |   |   |-node «term_=_», none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)

|   |-atom original: ⟨⟩⟨ ⟩-- ':='
-- intro?
|   |-node Lean.Parser.Term.sorry, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'sorry'
-/

/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |-node null, none
|   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |-node num, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- '0'
-/

/-- extracts blocks like `have .. : ∀ ids : typs, ... := by intro(s)...`. -/
def extractHaves (stx : Syntax) : Array Syntax :=
  let haves := stx.filter (·.isOfKind ``Lean.Parser.Term.haveIdDecl)
  haves.filter findForall --fun s => !(s.filter? findForall).isEmpty
  --(haves.map (·.filter? findForall)).flatten

inspect
example : True := by
  have : ∀ a : Nat, a = a := by intro; rfl
  trivial


elab "fh " cmd:command : command => do
  elabCommand cmd
  for h in extractHaves cmd do
    if let (#[vs, _ts], #[intros]) := getVarsAndInfos h then
      Meta.inspect _ts --vs[0]
      logWarningAt h m!"variables could merge with '{intros}' {← `(command| variable $(⟨vs[0]⟩))}"
      --logWarningAt intros m!"the '{intros}' here!"

/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node Lean.Parser.Term.forall, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '∀'
|   |   |   |   |-node null, none
|   |   |   |   |   |-node Lean.Parser.Term.explicitBinder, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- ')'
|   |   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ','
|   |   |   |   |-node «term_=_», none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |-atom original: ⟨⟩⟨ ⟩-- ':='

|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |   |-node Lean.Parser.Term.explicitBinder, none
|   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |-node null, none
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |-node null, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ')'
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node «term_=_», none
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |-atom original: ⟨⟩⟨ ⟩-- ':='

-/


set_option pp.rawOnError true

fh
inspect
example : True := by
  have : ∀ (test : Nat), test = test := by intros b; rfl
  trivial


inspect
example : True := by
  have (test : Nat) : test = test := by rfl
  trivial

fh
example : True := by
  have : ∀ test, (test : Nat) = test := by intros; rfl
  trivial


#check Lean.Parser.Command.declValSimple
fh
set_option linter.unusedVariables false in
--inspect
example : True := by
  have test (n : Nat) : ∀ test : Nat, test = test := by intros b; rfl
  have bad : ∃ d : Nat, ∀ bad b : Nat, ∀ c : Nat, bad = bad := by
    use 0
    intro a b c
    have good : ∀ {good : Nat}, good = good := by
      intro a
      exact rfl
    exact rfl
  have also_good : ∀ also_good another_good : Nat, also_good = also_good := by
    have also_bad : ∃ z : Nat, z = 0 := ⟨_, rfl⟩
    intro a _
    exact rfl
  have not : Nat := 0
  exact .intro
