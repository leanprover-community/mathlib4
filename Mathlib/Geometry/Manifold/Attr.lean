module

public meta import Lean

namespace Manifold.Elab

open Lean Elab

-- thunk approach?
-- IO.Ref?
-- scoped?

-- no environment extension, just attribute

public meta section

/--
Captures information when a model with corners is the trivial model on a normed space
(or on an inner product space, which is also a normed space):
contains the expressions describing the normed space and its base field.

Searching for a model with corners will return an `Option NormedSpaceInfo`,
which is `some` if and only if the trivial model on a normed space was found.
-/
structure NormedSpaceInfo where
  /-- The expression for the normed space itself. -/
  normedSpace : Expr
  /-- The expression for the normed space's base field. -/
  baseField   : Expr
deriving Inhabited

/--
Information about a model with corners found through `findModelInner`.
It includes the model with corners found, and, if this model is the trivial model with corners on a
normed space, information about that normed space. (Knowing this is important for forming products
of models.)

Most search results are not a model with corners for a normed space, so an `Expr` representing the
model with corners may be coerced directly to this type.
-/
structure FindModelResult where
  /-- Expression describing the model with corners found. -/
  model : Expr
  /-- Information on the underlying normed space,
  if this model is the trivial model with corners on a normed space. -/
  normedSpaceInfo? : Option NormedSpaceInfo := none
deriving Inhabited

instance : Coe Expr FindModelResult where
  coe model := { model }

abbrev FindModelStrategy := Expr → TermElabM FindModelResult

/-- Read a `find_model` extension from a declaration of the right type. -/
def mkFindModelStrategy (n : Name) : ImportM FindModelStrategy := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck FindModelStrategy opts ``FindModelStrategy n

initialize findModelExt : PersistentEnvExtension (Name × String) (FindModelStrategy × Name × String)
    (Array (FindModelStrategy × String) × List (Name × String)) ←
    registerPersistentEnvExtension {
  mkInitial := return (#[], [])
  addEntryFn := fun (s, newEntries) (strat, name, descr) =>
    (s.push (strat, descr), (name, descr)::newEntries)
  addImportedFn imported := do
    let mut s := #[]
    for entries in imported do
      for (decl, descr) in entries do
        let strat ← mkFindModelStrategy decl
        s := s.push (strat, descr)
    return (s, [])
  exportEntriesFn state := state.2.toArray}

syntax (name := find_model) "find_model " str : attr

--syntax (name := something) &"something" : term

--variable (something : Nat)

/-- Strategy for finding a model. -/
initialize registerBuiltinAttribute {
  name := `find_model
  descr := "Strategy for finding a model"
  add := fun decl stx kind => do
    match stx with
    | `(attr| find_model $s:str) =>
      unless kind == .global do throwAttrMustBeGlobal `find_model kind
      ensureAttrDeclIsMeta `find_model decl kind
      let strat ← mkFindModelStrategy decl
      modifyEnv fun env => findModelExt.addEntry env (strat, decl, s.getString)
    | _ => Elab.throwUnsupportedSyntax
  applicationTime := .afterCompilation}
