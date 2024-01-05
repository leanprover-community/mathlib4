import Mathlib.Tactic.Basic
import Std.Classes.SetNotation

/-- Notation typeclass for the heterogeneous `x +: xs` operation, frequently called "cons".
That is, add a single element to the front of a collection, where the resulting collection might
have a different type, e.g., to reflect the changed size -/
class HCons (C_in : Type*) (C_out : outParam Type*) (α : outParam Type*) where
  /-- `x +: xs` means to add a single element `x` to the front of collection `xs` -/
  hCons : α → C_in → C_out

@[inherit_doc] infixr:67 " +: " => HCons.hCons

/-- The `Insert` typeclass is a homogeneous `cons` operation -/
instance {C α : Type*} [Insert α C] : HCons C C α where
  hCons := insert

/-- Notation typeclass for heterogeneously appending a single element to the end of a collection:
`xs :+ x`
Heterogeneous in the sense that the resulting collection might have a different type, e.g.,
to reflect the changed size -/
class HAppendOne (C_in : Type*) (C_out : outParam Type*) (α : outParam Type*) where
  /-- `xs :+ x` means to add a single element `x` to the end of collection `xs` -/
  hAppendOne : C_in → α → C_out

@[inherit_doc] infixr:67 " :+ " => HAppendOne.hAppendOne

/-- Homogeneous verion of `AppendOne`: `xs :+ x : C` where `xs : C`. -/
class AppendOne (C : Type*) (α : outParam Type*) where
  /-- Add a single element to the front of a collection -/
  appendOne : C → α → C

instance {C α : Type*} [AppendOne C α] : HAppendOne C C α where
  hAppendOne := AppendOne.appendOne

/-- `AppendOne` is essentially the same as appending a singleton.  -/
instance {C α : Type*} [Singleton α C] [Append C] : AppendOne C α where
  appendOne xs x := xs ++ {x}
