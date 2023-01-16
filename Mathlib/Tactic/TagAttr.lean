/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# "Tag" attributes

Allow creating attributes using `register_tag_attr`,
and retrieving the array of `Name`s of declarations which have been tagged with such an attribute.

-/

namespace Mathlib.Tactic.TagAttr

open Lean

/-- An environment extension that just tracks an array of names. -/
abbrev TagExtension := SimpleScopedEnvExtension Name (Array Name)

/-- The collection of all current `TagExtension`s, indexed by name. -/
abbrev TagExtensionMap := HashMap Name TagExtension

/-- Store the current `TagExtension`s. -/
initialize tagExtensionMapRef : IO.Ref TagExtensionMap ← IO.mkRef {}

/-- Helper function for `registerTagAttr`. -/
def mkTagExt (name : Name := by exact decl_name%) : IO TagExtension :=
  registerSimpleScopedEnvExtension {
    name     := name
    initial  := #[]
    addEntry := fun d e => d.push e
  }

/-- Helper function for `registerTagAttr`. -/
def mkTagAttr (attrName : Name) (attrDescr : String) (ext : TagExtension)
  (ref : Name := by exact decl_name%) : IO Unit :=
registerBuiltinAttribute {
  ref   := ref
  name  := attrName
  descr := attrDescr
  applicationTime := AttributeApplicationTime.afterCompilation
  add   := fun declName _ _ =>
    ext.add declName
  erase := fun declName => do
    let s := ext.getState (← getEnv)
    modifyEnv fun env => ext.modifyState env fun _ => s.erase declName
}

/--
Construct a new "tag attribute",
which does nothing except keep track of the names of the declarations with that attribute.

Users will generally use the `register_tag_attr` macro defined below.
-/
def registerTagAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO TagExtension := do
  let ext ← mkTagExt ref
  mkTagAttr attrName attrDescr ext ref
  tagExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

/-- Initialize a new "tag" attribute.
Declarations tagged with the attribute can be retrieved using `Mathlib.Tactic.TagAttr.tagged`. -/
macro (name := _root_.Lean.Parser.Command.registerTagAttr) doc:(docComment)?
  "register_tag_attr" id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote (removeLeadingSpaces
    (doc.map (·.getDocString) |>.getD s!"tagged declarations for {id.getId.toString}"))
  `($[$doc:docComment]? initialize ext : TagExtension ←
      registerTagAttr $(quote id.getId) $descr $(quote id.getId)
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str : attr)

/-- When `attrName` is an attribute created using `register_tag_attr`,
return the names of all declarations tagged using that attribute. -/
def tagged (attrName : Name) : MetaM (Array Name) := do
  match (← tagExtensionMapRef.get).find? attrName with
  | none => throwError "No extension named {attrName}"
  | some ext => pure <| ext.getState (← getEnv)

/-- A dummy tag attribute, to ease testing. -/
register_tag_attr dummy_tag_attr
