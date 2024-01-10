/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Std.Data.Option.Basic
import Std.Tactic.HaveI

/-! # Flexible binders

This module provides a way for notations to use a flexible binder syntax
that can have notation-specific meanings and that is user-extensible.

The notation-specific meanings are implemented using a concept that's here called
a "domain type", which is intended to refer to the type used in bounded quantifiers.
For example, the domain type `finset` uses `Finset _` bounded quantifiers.
The default domain type is `type`, which does not make use of bounded quantifiers -- all
quantification is over the types themselves.
Notations are free to define their own domain types for their own purposes.

The extended binders `Std.ExtendedBinder.extBinders` have a similar aim,
but flexible binders are more general and accept a wider range of syntax,
including patterns.
For example, with flexible binders one can have a binder list
such as `a b (c d : e) (f g h ∈ i) (⟨j, k⟩ ∈ L)`.
Unlike `extBinders`, flexible binders are not concerned about whether the binder
notation overlaps with core binder notation, since it is meant to be used in user notation.
Like `extBinders`, flexible binders are only for explicit binders (so no implicits, strict
implicits, or instance arguments).

For debugging flexible binders, there is a command `#test_flexible_binders`.
For example, `#test_flexible_binders => x y z ∈ s` or `#test_flexible_binders finset => x y z ∈ s`.
-/

namespace Mathlib.FlexibleBinders
open Lean

/-- Syntax for general binder lists that support binder-like forms such as `(x ∈ s)`.
These are some examples of things that are meant to be supported by flexible binders:
- `x y z : Nat`
- `(x y : Nat) (z : Int)`
- `x y ∈ s`
- `(x : Nat) ∈ s`
- `(x, y) ∈ s`
- `((x, y) ∈ s) (z : Fin (x + y))`

Use `Mathlib.FlexibleBinders.expandFlexibleBinders` to parse `flexibleBinders`.

New binders are defined using the `declare_flexible_binder` command and/or
by defining macros for `binder%(...)` and `binderSplit%(...)`.

The syntax itself is very flexible and is (ab)using the fact that function application
can be used to represent a list of binders. The `fun` notation in core Lean uses a similar
encoding for its explicit binders. -/
-- Note: `term` is optional so that it is possible to encode zero binders.
syntax flexibleBinders := (term)? (" : " term)?

/-- If `stx` is of the form `a1 ... an` then returns `#[a1, ..., an]`,
otherwise returns `#[stx]`.
This is for handling sequences of binders.
(Note: `fun` binders (mis)use applications like this, for example in `(x y z : Nat)`). -/
def splitTerm (stx : Term) : Array Term :=
  match stx with
  | `($f $args*) => #[f] ++ args
  | _ => #[stx]

/-- Throw an error reporting that there is an unexpected type ascription.
The `ref` should be the type after the ascription. -/
def throwUnexpectedTypeAscription {α : Type} (ref : Syntax) : MacroM α :=
  Macro.throwErrorAt ref "Unexpected type ascription"

/-- If the `flexibleBinders` has a trailing type ascription (for example `x y z : α`)
then turn it into an actual type ascription (for example `(x y z : α)`).
Returns `none` if this is list of zero binders. -/
def elimAscription (b : TSyntax ``flexibleBinders) : MacroM (Option Term) :=
  match b with
  | `(flexibleBinders| $t:term :%$c $ty) => withRef b `(($t :%$c $ty))
  | `(flexibleBinders| $t:term) => return t
  | `(flexibleBinders| $[: $_]?) => return none
  | _ => Macro.throwUnsupported

/-- Category for "domain types" for flexible binders. -/
declare_syntax_cat flexibleBindersDom

/-- The `type%` domain type is for binders that only range over types.
Bounded quantifiers do not occur. -/
syntax "type%" : flexibleBindersDom

/-- The `finset%` domain type is for having bounded quantifiers that
range over `Finset`s. Binders can also range over types. -/
syntax "finset%" : flexibleBindersDom

/-- `binder%(DomainType, t)` is a term that represents a collection of simpler binders that
are an interpretation of the flexible binder `t`.
The `DomainType` is some name that is used to control how flexible binders are interpreted.
Here are some examples:
- `type` (the "default") only has unrestricted binders
- `set` allows binders quantifying over `Set`s
- `finset` allows binders quantifying over `Finset`s.

A `binder%(...)` expression may resolve into `binderResolved%(...)` and `binderMatch%(...)`
expressions. It can resolve into multiple of these expressions by using application syntax
or a null node (see `Mathlib.FlexibleBinders.combineBinders`).

By default, `binder%(DomainType, t)` expands to `binderResolved%(_, t)`. -/
scoped syntax (name := binderQuery) "binder%(" flexibleBindersDom ", " term ")" : term

/-- `binderSplit%(DomainType, t)` is a preprocessing step for `binder%(...)`.
This way `binder%(...)` itself doesn't worry about needing to split binders.
Expands to `binder%(DomainType, t)` by default. -/
scoped syntax (name := binderSplitQuery) "binderSplit%(" flexibleBindersDom ", " term ")" : term

/-- `binderResolved%(ty, b, dom?)` is a possible expansion of `binder%(...)`,
where `ty` is the type of the binder `b`
and `dom?`, if present, is the domain that `b` ranges over.
The type of the domain is governed by the `DomainType` that was passed to `binder%(...)`

If `DomainType` is `type`, then `dom?` should always be absent.
This result corresponds to a `(b : dom)` binder.

The `b` can be any expression, and if it is not a hole or identifier it is
realized as a pattern match.

In the variant `binderResolved%(p)`, then `p` is a `Prop` and the notation that
is using flexible binders is free to represent it with some non-dependent construction. -/
scoped syntax (name := binderResolution)
  "binderResolved%(" term (", " term (", " term)?)? ")" : term

/-- `binderMatch%(discr, patt)` is a possible expansion of `binder%(...)`,
and rather than representing a binder per se,
this represents the directive that a `match` expression must
be inserted to implement pattern matching.
It should be realized as `match discr with | patt => ...`. -/
scoped syntax "binderMatch%(" term ", " term ")" : term

/-- `binderLetI%(name, val)` is a possible expansion of `binder%(...)`,
and rather than representing a binder per se,
this represents the directive that a `letI` expression must be inserted.
It should be realized as `letI name := val; ...`. -/
scoped syntax "binderLetI%(" ident ", " term ")" : term

/-- A record of an individual binder after expansion of `flexibleBinders`. -/
inductive Binder where
  /-- This is a standard binder.
  - `ty` is the type of the binder
  - `binder` is an identifier or a hole
  - `dom?`, if present, is a term representing the domain that the binder ranges
    over. If absent, then `binder` ranges over all of `ty`.
    The type of `dom` is controlled by the `DomainType` during expansion. -/
  | std (ty : Term) (binder : Term) (dom? : Option Term)
  /-- An anonymous binder with a `Prop` domain. This lets notation use some non-dependent
  construction, for example using `And` in an `Exists`. -/
  | prop (p : Term)
  /-- Instruction to insert a `match` expression with the given discriminant and pattern.
  In particular, `match discr with | patt => ...`. -/
  | match (discr : Term) (patt : Term)
  /-- Instruction to insert a `letI` expression.
  In particular, `letI name := val; ...`. -/
  | letI (name : Ident) (val : Term)

instance : Inhabited Binder := ⟨.prop <| Unhygienic.run `(True)⟩

/-- Takes a term and interprets it as a flexible binder expression.
Uses the `binder%(...)`/`binderSplit%(...)` syntax to process and expand binders.
- `domainType` is usually `type`, which turns off bounded quantification.
  In some applications (like for `Finset.sum`) we might use other values (like `finset`).
- `bi` is the expression to expand.
  If it is a function application then it is interpreted as being a sequence of binders.

Only unresolved `binder%(...)`/`binderSplit%(...)` expressions are macro expanded -- macros
are not expanded in general.
This decision can be revisited if there is an application for doing full macro expansion.

If `bi` is a function application it is interpreted as a sequence of binders.
If `bi` is a null node it is interpreted as a sequence of binders. -/
partial def expandBinder (domainType : TSyntax `flexibleBindersDom) (bi : Term) :
    MacroM (Array Binder) := do
  process #[] bi
where
  process (acc : Array Binder) (bi : Term) : MacroM (Array Binder) := withRef bi do
    match bi with
    | `(binder%($_, $t)) =>
      match ← expandMacro? bi with
      | some bi' => process acc ⟨bi'⟩
      | none => process acc (← `(binderResolved%(_, $t)))
    | `(binderSplit%($dom, $t)) =>
      match ← expandMacro? bi with
      | some bi' => process acc ⟨bi'⟩
      | none => process acc (← `(binder%($dom, $t)))
    | `(binderResolved%($ty, $binder $[, $dom?]?)) =>
      match binder with
      | `(_) | `($_:ident) => return acc |>.push (Binder.std ty binder dom?)
      | _ => withFreshMacroScope <| withRef binder do
        -- It's a pattern, so create a new variable and set up a `match`.
        let x ← `(x)
        return acc |>.push (Binder.std ty x dom?) |>.push (Binder.match x binder)
    | `(binderResolved%($p)) =>
      return acc |>.push (Binder.prop p)
    | `(binderMatch%($discr, $patt)) => return acc.push <| Binder.match discr patt
    | `(binderLetI%($name, $val)) => return acc.push <| Binder.letI name val
    | `($f $args*) =>
      let acc ← process acc f
      args.foldlM (init := acc) process
    | _ =>
      if bi.raw.isOfKind nullKind then
        bi.raw.getArgs.foldlM (init := acc) (process · ⟨·⟩)
      else
        -- This is some term we haven't begun to process,
        -- so wrap it in `binderSplit%(...)` to initialize.
        process acc (← `(binderSplit%($domainType, $bi)))

/-- Interprets a `flexibleBinders` term as an array of binders.

This is a frontend to `expandBinder` that handles the trailing ascription
in `Mathlib.FlexibleBinders.expandBinder`. See the documentation there for an explanation
of `domainType`. -/
def expandFlexibleBinders
    (domainType : TSyntax `flexibleBindersDom) (b : TSyntax ``flexibleBinders) :
    MacroM (Array Binder) := do
  match ← elimAscription b with
  | some b' => expandBinder domainType b'
  | none => return #[]

/-- Command to test flexible binders.
For example, `#test_flexible_binders => x y z : Nat`
or `#test_flexible_binders finset% => x y z ∈ Nat`. -/
elab "#test_flexible_binders " dom?:(flexibleBindersDom)? " => " e:flexibleBinders : command => do
  let dom ← dom?.getDM `(flexibleBindersDom| type%)
  let res ← Elab.liftMacroM <| expandFlexibleBinders dom e
  for r in res do
    match r with
    | .std ty binder none =>
      logInfo m!"binder {← `(($binder : $ty))}"
    | .std ty binder (some domain) =>
      logInfo m!"binder {← `(($binder : $ty))} ∈ {domain}"
    | .prop p => logInfo m!"prop binder {← `((_ : $p))}"
    | .match discr patt => logInfo m!"match {discr} with | {patt} => ..."
    | .letI name val => logInfo m!"letI {name} := {val}; ..."

/-- Uses a null node to encode a list of binders.
This is suitable as a return value in `binder%(...)` expansions to return multiple binders. -/
def combineBinders (bis : Array Term) : Term :=
  ⟨mkNullNode bis⟩

/-- Convert a list of binders back into a `flexibleBinders`. -/
def encodeBinders {m : Type → Type} [Monad m] [MonadQuotation m]
    (bis : Array Term) : m (TSyntax ``flexibleBinders) :=
  if bis.isEmpty then
    `(flexibleBinders| )
  else
    let f := bis[0]!
    let xs := bis.extract 1 bis.size
    `(flexibleBinders| $(Syntax.mkApp f xs):term)

/-- Given `(e : ty)` returns `(e, ty)`. Otherwise returns `(t, _)`. -/
def destructAscription (t : Term) : MacroM (Term × Term) :=
  match t with
  | `(($e : $ty)) => return (e, ty)
  | _ => do return (t, ← withRef t `(_))

/-- Strip parentheses if it's not of the form `(x1 ... xn)` where one of `x1`,...,`xn`
is a global identifier (we don't strip parentheses when this could possibly be a pattern). -/
macro_rules
  | `(binderSplit%($domType, ($e))) => do
    let es := splitTerm e
    -- Note: getId returns anonymous for non-identifiers
    let notPatt ← es.allM fun id => do return List.isEmpty (← Macro.resolveGlobalName id.raw.getId)
    unless notPatt do Macro.throwUnsupported
    return combineBinders <| ← es.mapM fun e' => withRef e'.raw `(binderSplit%($domType, $e'))

/-- Sets up expanding `(x y z : α)` to `(x : α) (y : α) (z : α)`. -/
macro_rules
  | `(binderSplit%($domType, ($x $xs* : $ty))) => do
    let xs := #[x] ++ xs
    return combineBinders <| ← xs.mapM fun b => withRef b.raw `(binder%($domType, ($b : $ty)))

/-- For all domains, `(x : ty)` is a binder over the type `ty` itself. -/
macro_rules
  -- This first rule is to help catch errors such as `(x ∈ s) : α`.
  -- It is in collaboration with a rule defined by `declare_flexible_binder`.
  | `(binder%($domType, (($e) : $ty))) => `(binder%($domType, ($e : $ty)))
  | `(binder%($_, ($e : $ty))) => do
    if e matches `(($_ : $_)) then throwUnexpectedTypeAscription ty
    `(binderResolved%($ty, $e))

/-- Sets up Prop flexible binders.

Example: `declare_flexible_binder x => $x ∈ $ty`.
- Sets up expanding `(x y z ∈ s)` to `(x ∈ s) (y ∈ s) (z ∈ s)`.
- Sets up default expanders with, for example, `(x ∈ s)` as `(x : _) (_ : x ∈ s)`.
  The `(x : _)` here is expanded as ` binder%(...)` so that the current domain type still
  has a chance to provide a custom expansion.
- Sets up throwing an error for terms like `((x ∈ s) : α)`.
- Handles constructs such as `(x : α) ∈ s` as well as
  expanding `(x y : α) ∈ s` as `((x : α) ∈ s) ((y : α) ∈ s)`. -/
macro "declare_flexible_binder " b:ident " => " t:term : command => do
  `(macro_rules
    | `(binderSplit%($$domType, $t)) => do
      match $b:term with
      | `($$x $$xs*) =>
        let xs := #[x] ++ xs
        return combineBinders <| ← xs.mapM fun $b => withRef ($b).raw `(binderSplit%($$domType, $t))
      | `(($$x $$xs* : $$ty)) =>
        -- For expanding things such as `(x y : Nat) ∈ s` to `((x : Nat) ∈ s) ((y : Nat) ∈ s)`
        let xs := #[x] ++ xs
        return combineBinders <| ← xs.mapM fun x => withRef ($b).raw do
          let $b ← `(($$x : $$ty))
          `(binder%($$domType, $t))
      | _ => Macro.throwUnsupported
    | `(binder%($$_, ($t : $$ty))) =>
      -- This is to exclude syntax such as `(x ∈ s) : Nat` and `(x ≤ 37) : Nat`.
      throwUnexpectedTypeAscription ty
    | `(binder%($$domType, $t)) => do
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
