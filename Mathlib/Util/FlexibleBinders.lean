/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
--import Std.Util.ExtendedBinder
-- import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Basic

/-! # Flexible binders

This module provides a way for notations to use a flexible binder syntax that
can have notation-specific meanings and that is user-extensible.

The extended binders `Std.ExtendedBinder.extBinders` have a similar aim,
but flexible binders are more general and accept a wider range of syntax.
For example, with flexible binders one can have a binder list
such as `a b (c d : e) (f g h ∈ i)`.
Unlike `extBinders`, flexible binders are not concerned about whether the binder
notation overlaps with core binder notation, since it is meant to be used in user notation.
Like `extBinders`, flexible binders are only for explicit binders (so no implicits, strict
implicits, or instance arguments).
-/

namespace Mathlib.FlexibleBinders
open Lean Meta

/-- Syntax for general binder lists that support binder-like forms such as `(x ∈ s)`.
These are some examples of things that are meant to be supported by flexible binders:
- `x y z : Nat`
- `(x y : Nat) (z : Int)`
- `x y ∈ s`
- `(x, y) ∈ s`
- `((x, y) ∈ s) (z : Fin (x + y))`

The syntax itself is very flexible and is (ab)using the fact that function application
can be used to represent a list of binders. This follows how core uses such an encoding
for explicit binders in `fun` notation. -/
syntax flexibleBinders := term (" : " term)?

/-- If `stx` is of the form `a1 ... an` then returns `#[a1, ..., an]`,
otherwise returns `#[stx]`.
This is for handling sequences of binders.
(Note: `fun` binders (mis)use applications like this, for example in `(x y z : Nat)`). -/
def splitTerm (stx : Term) : Array Term :=
  match stx with
  | `($f $args*) => #[f] ++ args
  | _ => #[stx]

/-- If the `flexibleBinders` has a trailing type ascription (for example `x y z : α`)
then turn it into an actual type ascription (for example `(x y z : α)`). -/
def elimAscription (b : TSyntax ``flexibleBinders) : MacroM Term :=
  match b with
  | `(flexibleBinders| $t :%$c $ty) => withRef b `(($t :%$c $ty))
  | `(flexibleBinders| $t:term) => return t
  | _ => Macro.throwUnsupported

/-- `binder%(DomainType, t)` is a term that represents a collection of simpler binders that
are an interpretation of the term `t` as a flexible binder.
The `DomainType` is some name that is used to control how flexible binders are interpreted.
The "default" is `DomainType` being `type`, where domains are types.
Another that is in use is `finset`, where domains are `Finset`s.

A `binder%(...)` expression may resolve into `binderResolved%(...)` and `binderMatch%(...)`
expressions. It can resolve into multiple of these expressions by using application syntax. -/
scoped syntax (name := binderQuery) "binder%(" ident ", " term ")" : term

/-- `binderDefault%(DomainType, t)` is for handling the default case, when no other
macros for `binder%(...)` match. -/
scoped syntax (name := binderDQuery) "binderDefault%(" ident ", " term ")" : term

/-- `binderResolved%(dom, b)` is a possible expansion of `binder%(...)`,
where `b` is the binder and `dom` is a domain that is appropriate for the `DomainType`.
If `DomainType` is `type`, then this result corresponds to a `(b : dom)` binder.
The `b` can be any expression, and if it is not a hole or identifier it is
realized as a pattern match.

In the variant `binderResolved%(dom)`, then `dom` is a `Prop` and the notation using flexible
binders is free to turn it into some non-dependent construction. -/
scoped syntax (name := binderResolution) "binderResolved%(" term (", " term)? ")" : term

/-- `binderMatch%(discr, patt)` is a possible expansion of `binder%(...)`,
and rather than representing a binder it is a directive that a `match` expression must
be inserted to implement some pattern matching.
It should be realized as `match discr with | patt => ...`. -/
scoped syntax "binderMatch%(" term ", " term ")" : term

/-- A record of an individual binder after expansion of `flexibleBinders`. -/
inductive Binder where
  /-- This is a standard binder.
  - `domain` is a term to use as the domain for the binder.
    The type of `domain` depends on the "domain type" used when expanding the flexible binders.
    For example, for `type` it is the type of `binder`, but for `finset` it is a `Finset` that
    the `binder` ranges over.
  - The `binder` should be an identifier or a hole. -/
  | std (domain : Term) (binder : Term)
  /-- An anonymous binder with a `Prop` domain. This lets notation use some non-dependent
  construction, for example using `And` in an `Exists`. -/
  | prop (p : Term)
  /-- Instruction to insert a `match` expression with the given discriminant and pattern.
  In particular, `match discr with | patt => ...`. -/
  | match (discr : Term) (patt : Term)

/-- Takes a term and interprets it as a flexible binder expression.
Uses the `binder%(...)` mechanism to process and expand binders.
- `domainType` is usually `type`, meaning the domains are types.
  In some applications (like for `Finset.sum`) we might use other values (like `finset`).
- `bi` is the expression to expand.
  If it is a function application then it is interpreted as being a sequence of binders.

Only unresolved `binder%(...)` expressions are macro expanded -- macros are not expanded in general.
This decision can be revisited if there is an application for doing full macro expansion. -/
partial def expandBinder (domainType : Name := `type) (bi : Term) : MacroM (Array Binder) := do
  process #[] bi
where
  process (acc : Array Binder) (bi : Term) : MacroM (Array Binder) := withRef bi do
    match bi with
    | `(binder%($_, $_)) | `(binderDefault%($_, $_)) =>
      match ← expandMacro? bi with
      | some bi' => process acc ⟨bi'⟩
      | none => Macro.throwErrorAt bi "Invalid binder"
    | `(binderResolved%($domain, $binder)) =>
      match binder with
      | `(_) | `($_:ident) => return acc |>.push (Binder.std domain binder)
      | _ => withFreshMacroScope <| withRef binder do
        -- It's a pattern, so create a new variable and set up a `match`.
        let x ← `(x)
        return acc |>.push (Binder.std domain x) |>.push (Binder.match x binder)
    | `(binderResolved%($domain)) =>
      return acc |>.push (Binder.prop domain)
    | `(binderMatch%($discr, $patt)) => return acc.push <| Binder.match discr patt
    | `($f $args*) =>
      let acc ← process acc f
      args.foldlM (init := acc) process
    | _ =>
      -- This is some term we haven't begun to process,
      -- so wrap it in `binder%(...)` to initialize.
      process acc (← `(binder%($(mkIdent domainType), $bi)))

/-- Frontend to `expandBinder` that handles the trailing ascription in `flexibleBinders`. -/
def expandFlexibleBinders (domainType : Name := `Type) (b : TSyntax ``flexibleBinders) :
    MacroM (Array Binder) := do
  let b' ← elimAscription b
  expandBinder domainType b'

/-- Command to test flexible binders.
For example, `#test_flexible_binders type => x y z : Nat`. -/
elab "#test_flexible_binders " dom:ident " => " e:flexibleBinders : command => do
  let res ← Elab.liftMacroM <| expandFlexibleBinders dom.getId e
  for r in res do
    match r with
    | .std domain binder => logInfo m!"domain = {domain}, binder = {binder}"
    | .prop p => logInfo m!"prop domain = {p}"
    | .match discr patt => logInfo m!"match {discr} with | {patt} => ..."

/-- Encodes the given list of binders as a function application.
This is suitable as a return value in `binder%(...)` expansions to return multiple binders. -/
def returnBinders (bis : Array Term) : MacroM Term := do
  if bis.size == 0 then
    Macro.throwError "Cannot expand into zero binders"
  else if bis.size == 1 then
    return bis[0]!
  else
    `($(bis[0]!) $(bis.extract 1 bis.size)*)

/-- Given `(e : ty)` returns `(e, ty)`. Otherwise returns `(t, _)` -/
def destructAscription (t : Term) : MacroM (Term × Term) :=
  match t with
  | `(($e : $ty)) => return (e, ty)
  | _ => do return (t, ← withRef t `(_))

/-- Default case: switch to using a default handler for the domain. -/
macro_rules
  | `(binder%($domType, $e)) => `(binderDefault%($domType, $e))

/-- Strip parentheses if it's not of the form `(x1 ... xn)` where one of `x1`,...,`xn`
is a global identifier (we don't strip parentheses when this could possibly be a pattern). -/
macro_rules
  | `(binder%($domType, ($e))) => do
    let es := splitTerm e
    let notPatt ← es.allM fun id => do return List.isEmpty (← Macro.resolveGlobalName id.raw.getId)
    unless notPatt do Macro.throwUnsupported
    returnBinders <| ← es.mapM fun e' => withRef e'.raw `(binder%($domType, $e'))

/-- Sets up expanding `(x y z : α)` to `(x : α) (y : α) (z : α)`. -/
macro_rules
  | `(binder%($domType, ($x $xs* : $ty))) => do
    let xs := #[x] ++ xs
    returnBinders <| ← xs.mapM fun b => withRef b.raw `(binder%($domType, ($b : $ty)))

/-- Default case for the type domain: the expression is a hole, ident, or more generally a pattern.
If it is a pattern, then `expandBinder` will later register the need for a `match` expression. -/
macro_rules
  | `(binderDefault%(type, $e)) => `(binderResolved%(_, $e))

/-- For the `type` domain, `(x : ty)` is a binder over `ty` itself. -/
macro_rules
  | `(binder%(type, ($e :%$c $ty))) => do
    if e matches `($_ $_*) then Macro.throwUnsupported
    if e matches `(($_ : $_)) then Macro.throwErrorAt c "Unexpected type ascription"
    `(binderResolved%($ty, $e))

/-- Sets up Prop flexible binders.

Example: `declare_flexible_binder x => $x ∈ $ty`.
- Sets up expanding `(x y z ∈ s)` to `(x ∈ s) (y ∈ s) (z ∈ s)`.
- Sets up default expanders with, for example, `(x ∈ s)` as `(x : _) (_ : x ∈ s)`.
  The `(x : _)` here is expanded as ` binder%(...)` so that the current domain type still
  has a chance to provide a custom expansion.
- Handles constructs such as `(x : α) ∈ s` and expanding `(x y : α) ∈ s`. -/
macro "declare_flexible_binder " b:ident " => " t:term : command => do
  `(macro_rules
    | `(binder%($$domType, $t)) => do
      match $b:term with
      | `($$x $$xs*) =>
        let xs := #[x] ++ xs
        returnBinders <| ← xs.mapM fun $b => withRef ($b).raw `(binder%($$domType, $t))
      | `(($$x $$xs* : $$ty)) =>
        -- For expanding things such as `(x y : Nat) ∈ s` to `((x : Nat) ∈ s) ((y : Nat) ∈ s)`
        let xs := #[x] ++ xs
        returnBinders <| ← xs.mapM fun x => withRef ($b).raw do
          let $b ← `(($$x : $$ty))
          `(binder%($$domType, $t))
      | _ => do
        let ($b, ty) ← destructAscription $b
        match $b:term with
        | `($$_:ident) => `(binder%($$domType, ($$($b) : $$ty)) binderResolved%($t))
        | `(_) => withFreshMacroScope do
          let $b ← `(x)
          `(binder%($$domType, (x : $$ty)) binderResolved%($t))
        | _ => withFreshMacroScope do
          let res ← do let $b ← `(x); `(binderResolved%($t))
          `(binder%($$domType, (x : $$ty)) $$res binderMatch%(x, $$($b))))

declare_flexible_binder x => $x < $y
declare_flexible_binder x => $x ≤ $y
declare_flexible_binder x => $x > $y
declare_flexible_binder x => $x ≥ $y
declare_flexible_binder x => $x ∈ $s

/-- The default handler for the `finset` is to use `Finset.univ` and hope for the best! -/
macro_rules
  | `(binderDefault%(finset, $e)) => `(binderResolved%(Finset.univ, $e))

/-- For the `finset` domain, `(x : ty)` is a binder over `Finset.univ` for `ty`. -/
macro_rules
  | `(binder%(finset, ($e :%$c $ty))) => do
    if e matches `($_ $_*) then Macro.throwUnsupported
    if e matches `(($_ : $_)) then Macro.throwErrorAt c "Unexpected type ascription"
    `(binderResolved%((Finset.univ : Finset $ty), $e))

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck ExtendedBinder2.finsetStx] def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax

/-- For the `finset` domain, `(x ∈ s)` is a binder over `s` as a `Finset`. -/
macro_rules
  | `(binder%(finset, $e ∈ $s)) => do
    let (e, ty) ← destructAscription e
    if e matches `($_ $_*) then Macro.throwUnsupported
    `(binderResolved%((finset% $s : Finset $ty), $e))

/-- For the `finset` domain, `a + b = n` for sums over the antidiagonal. -/
macro_rules
  | `(binder%(finset, $a + $b = $n)) =>
    `(binder%(finset, ($a, $b) ∈ Finset.Nat.antidiagonal $n))

#test_flexible_binders type => x y z
#test_flexible_binders finset => x y z
#test_flexible_binders type => x y z : α
#test_flexible_binders finset => x y z : α
#test_flexible_binders type => x y z ∈ s
#test_flexible_binders finset => x y z ∈ s
#test_flexible_binders type => (x, y) ∈ s
#test_flexible_binders finset => (x, y) ∈ s

#test_flexible_binders type => (x : Nat) (y : Nat) ∈ s
#test_flexible_binders finset => (x : Nat) (y : Nat) ∈ s
#test_flexible_binders type => (x y : Nat) ∈ s
#test_flexible_binders finset => (x y : Nat) ∈ s

#test_flexible_binders type => (rfl)
#test_flexible_binders type => (x)

#test_flexible_binders finset => x + y = 5
#test_flexible_binders finset => (x + y = 5) (z ∈ s x y)

#test_flexible_binders type => (x : Nat) : Nat
#test_flexible_binders finset => (x : Nat) : Nat

#test_flexible_binders type => (p ∈ s) (x : Fin p.1)

macro "∃' " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `type bs
  res.foldrM (init := t) fun
    | .std dom bind, body => `(Exists fun ($bind : $dom) => $body)
    | .prop dom, body => `($dom ∧ $body)
    | .match discr patt, body => `(match $discr:term with | $patt => $body)

macro "∑ " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `finset bs
  res.foldrM (init := t) fun
  | .std dom bind, body => `(Finset.sum $dom fun $bind => $body)
  | .prop dom, body => `(if $dom then $body else 0)
  | .match discr patt, body => `(match $discr:term with | $patt => $body)

section
variable (s : Set (Nat × Nat))
#check ∃' (p ∈ s) (x : Fin p.1), x = p.2
#check ∃' p q ∈ s, p.1 + q.2 = 10
#check ∃' (x, y) ∈ s, x + y = 10
#check ∃' p ∈ s, True ∧ False
end

section
variable (s : Finset Nat) (s' : Set Nat) [Fintype s'] (f : Fin 37 → Nat)
#check ∑ x y ∈ s, x * y
#check ∑ x y ∈ s', x * y
#check ∑ x + y = 10, x * y
#check ∑ (x : Fin 37) (x x x : Fin x), x.1
#check ∑ (x y : Nat) ∈ s, x * y
#check ∑ x, f x
#check ∑ x < 10, f x
end
