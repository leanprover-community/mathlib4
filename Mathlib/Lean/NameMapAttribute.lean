/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean

namespace Lean

/-- Maps declaration names to α. -/
def NameMapExtension (α : Type) := SimplePersistentEnvExtension (Name × α) (NameMap α)

instance : Inhabited (NameMapExtension α) :=
  inferInstanceAs <| Inhabited (SimplePersistentEnvExtension ..)

def NameMapExtension.find? (ext : NameMapExtension α) (env : Environment) : Name → Option α :=
  (SimplePersistentEnvExtension.getState ext env).find?

/-- Add the given k,v pair to the NameMapExtension. -/
def NameMapExtension.add [Monad M] [MonadEnv M] [MonadError M]
  (ext : NameMapExtension α) (k : Name) (v : α) :  M Unit := do
  if let some _ := ext.find? (←getEnv) k then
    throwError "Already exists entry for {ext.name} {k}"
  else
     ext.addEntry (←getEnv) (k, v) |> setEnv

def mkNameMapExtension (α) (name : Name): IO (NameMapExtension α) := do
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun ass => ass.foldl (init := ∅) fun
                       | names, as => as.foldl (init := names) fun
                         | names, (a,b) => names.insert a b,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray
  }

structure NameMapAttributeImpl (α : Type) where
  name : Name
  descr : String
  add : (src : Name) → (stx : Syntax) →  AttrM α
  deriving Inhabited

/-- Similar to ParametricAttribute except that attributes do not
have to be assigned in the same file as the declaration. -/
structure NameMapAttribute (α) where
  impl : NameMapAttributeImpl α
  ext : NameMapExtension α
  deriving Inhabited

def NameMapAttribute.find? (attr : NameMapAttribute α)
  : (env : Environment) → Name → Option α := attr.ext.find?

def NameMapAttribute.add [Monad M] [MonadEnv M] [MonadError M]
  (attr : NameMapAttribute α) (k : Name) (v : α) : M Unit :=
  attr.ext.add k v

def registerNameMapAttribute (impl : NameMapAttributeImpl α) : IO (NameMapAttribute α) := do
  let ext ← mkNameMapExtension α impl.name
  registerBuiltinAttribute {
    name := impl.name
    descr := impl.descr
    add := fun src stx _kind => do
      let a : α ← impl.add src stx
      ext.add src a
  }
  return {
    impl := impl
    ext := ext
  }


end Lean
