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

def getIntroVars : Syntax → Option (Array Syntax)
  | `(by $first; $_*) =>
    if introTacs.contains first.raw.getKind then
      some (first.raw.filter (·.isOfKind `ident))
    else
      none
  | _ => none

inspect
example : ∀ a b c d : Nat, a + b = c + d := by
  skip
  intro a b
  intros c
  intro
  sorry

/-
|-node Lean.Parser.Tactic.intro, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'intro'
|   |-node null, none
|   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |-ident original: ⟨⟩⟨\n  ⟩-- (b,b)

|-node Lean.Parser.Tactic.intros, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'intros'
|   |-node null, none
|   |   |-ident original: ⟨⟩⟨\n  ⟩-- (c,c)
-/

def dropIntroVars : Syntax → Option Syntax
  | stx@(.node s1 k #[intr, .node s2 `null vars]) =>
    let varsDropFirst := vars.erase (vars.getD 0 .missing)
    let skipStx := mkNode ``Lean.Parser.Tactic.skip #[mkAtom "skip"]
    let newIntro : Syntax :=  -- recreate `intro [one fewer variable]`, even if input is `intros`
      .node s1 ``Lean.Parser.Tactic.intro #[mkAtomFrom intr "intro", .node s2 `null varsDropFirst]
    match k, vars.size with
      | ``Lean.Parser.Tactic.intros, 0 =>
        stx -- `intros` stays `intros`
      | ``Lean.Parser.Tactic.intros, 1 =>
        some skipStx -- `intros x` converts to `skip`
      | ``Lean.Parser.Tactic.intros, _ =>
        some newIntro -- `intros x ...` converts to `intro ...`
      | ``Lean.Parser.Tactic.intro, 0 | ``Lean.Parser.Tactic.intro, 1 =>
        some skipStx -- `intro` and `intro x` convert to `skip`
      | ``Lean.Parser.Tactic.intro, _ =>
        some newIntro -- `intro x y ...` converts to `intro y ...`
      | _, _ => none
  | _ => none

elab "fin " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter fun s => (introTacs.contains (s.getKind))
  for h in haves do
    logInfo m!"'{h}': '{dropIntroVars h}'"





example : ∀ a : Nat, (h : a = 0) → a = 0 := by
  introv
  intro h
  exact h

example : ∀ a : Nat, (h : a = 0) → a = 0 := by
  intros
  assumption

example : ∀ a : Nat, (h : a = 0) → a = 0 := by
  intro
  intro
  assumption


fin
--inspect
example : ∀ a b c d  e : Nat, a + b = c + d + e := by
  skip
  intro
  intro a b
  intros c
  intro
  intros
  sorry


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
  dbg_trace first
  (haveIds.push ⟨first.raw⟩, foralls.erase first, body, value)

def allStxCore (cmd : Syntax) : Syntax → CommandElabM (Option (Syntax × Syntax))
  | stx@`(tactic| have $id:haveId $bi1* : ∀ $bi2*, $body := $t) => do
    dbg_trace "bi1: '{bi1}'\nbi2: '{bi2}'\n"
    let (bi1', bi2', body', t') := recombineBinders bi1 bi2 body t
    --let ident := mkIdent `hyp
    let t := ← match t with
              | `(by $first; $ts*) => do
                if introTacs.contains first.raw.getKind then
                  return first.raw.filter (·.isOfKind `ident)
                else
                  return #[]
--                Meta.inspect first
--                match first with
--                  | `(tactic| intros $vs) =>
--                    dbg_trace "variables found: {vs}"
--                    return first
--                  | _ => dbg_trace "no vars found"; return first
              | _ => return default
    dbg_trace "variables found: {t}"
    let newHave := ←
      if bi2'.isEmpty then `(tactic| have $id:haveId $[$bi1']* : $body' := $t')
      else `(tactic| have $id:haveId $[$bi1']* : ∀ $[$bi2']*, $body' := $t')
    let newCmd ← cmd.replaceM fun s => do if s == stx then return some newHave else return none
    logInfo m!"command: {cmd}\nstx: {stx}\nnewCmd: {newCmd}\n"
    let s ← modifyGet fun st => (st, { st with messages := {} })
    elabCommandTopLevel newCmd
    let msgs ← modifyGet (·.messages, s)
    if msgs.hasErrors then
      logInfo m!"{← (msgs.unreported.filter (·.severity matches .error)).toArray.mapM (·.toString)}"
      return none
    else
      return some (newCmd, newHave)
  | _ => return none

partial
def allStx (cmd stx : Syntax) : CommandElabM Syntax := do
  match ← allStxCore cmd stx with
    | none => return stx
    | some (cmd, stx) => allStx cmd stx

elab "fh " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter (·.isOfKind ``Lean.Parser.Tactic.tacticHave_)
  for stx in haves do
--  if let some stx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    dbg_trace "found have"
    let newHave ← allStx cmd stx
    --logInfo newHave
    let newCmd ← cmd.raw.replaceM fun s => do if s == stx then return some newHave else return none
    logInfo m!"Elaborating '{newCmd}'"

-- and the test is successful!
fh
--inspect
example : True := by
  have (_ : Nat) : ∀ x y, x + y = 0 := by
    intros s t
    sorry
  trivial

fh
--inspect
example : True := by
  have : ∀ (n : Nat), n = n := by
    intro s
    rfl
  trivial

fh
--inspect
example : True := by
  have :  ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
  trivial

example : True :=
  by
  have (k : Nat) _ : ‹_› = k := by
    intros
    sorry
  trivial

example : True := by
  have _ : ‹_› = 0 := by
    intros
    sorry
  trivial

example {n : Nat} : True :=
  by
  have {_} : ‹_› = 0 := by
    intro x
    sorry
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
