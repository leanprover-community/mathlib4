import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Lean

universe v u

open CategoryTheory AlgebraicGeometry

variable (C : Type u) [Category.{v} C]

open Lean Elab Command in
elab "mkMorphismProperty " cmd:command : command => do
  let oldName := (cmd.raw.find? (·.isOfKind ``Parser.Command.declId)).getD default
  let className := mkIdentFrom oldName (oldName[0].getId ++ `class)
  -- replaces the given name with `name.class`
  let withClassName ← cmd.raw.replaceM fun s =>
    if s.isOfKind ``Parser.Command.declId then return some className else return none
  -- elaborates the `.class` syntax
  elabCommand withClassName
  -- Now need to find which category the morphism is taking place in.
  -- Can safely assume that the final argument is the morphism.




  let newAbbrev ←
    `(command| abbrev $(⟨oldName⟩) : $(mkIdent `MorphismProperty) $(mkIdent `Scheme) := $className)
  elabCommand newAbbrev

mkMorphismProperty
class Foo {X Y : Scheme} (f : X ⟶ Y) : Prop where

#check Foo
#check Foo.class
