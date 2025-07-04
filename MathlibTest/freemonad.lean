import Mathlib.Control.Monad.Free.Effects
import Mathlib.Data.String.Defs

open FreeM

-- Example FreeState computations

example : FreeState.evalState (do
  let s ← get
  set (s + 1)
  return s : FreeState Nat Nat) 5 = 5 := by simp


example : FreeState.runState (do
  let s ← get
  set (s + 1)
  return s : FreeState Nat Nat) 5 = 6 := by simp


example : FreeState.run (do
  let s ← get
  set (s + 1)
  return s : FreeState Nat Nat) 5 = (5, 6) := by simp

-- Example FreeWriter computations

private instance instMonoidString : Monoid String where
  mul := String.append
  mul_assoc := String.append_assoc
  one := ""
  one_mul := String.empty_append
  mul_one := String.append_empty

@[simp]
lemma mul_append (a b : String) : a * b = a ++ b := rfl

@[simp]
lemma append_empty (a : String) : a ++ 1 = a := String.append_empty a

example : FreeWriter.run (do
  FreeWriter.tell "Hello, "
  FreeWriter.tell "World!"
  return 42) = (42, "Hello, World!") := by simp

example : FreeWriter.run (do
  let (x, captured) ← FreeWriter.listen (do
    FreeWriter.tell "Hello, "
    return 42)
  FreeWriter.tell "World!"
  return (x, captured)) = ((42, "Hello, "), "Hello, World!") := by simp

example : FreeWriter.run (FreeWriter.pass (do
  FreeWriter.tell "Hello"
  return ((), fun (w : String) => w ++ "!"))) = ((), "Hello!") := by simp

-- Example FreeCont computations

example : FreeCont.run (do
  FreeCont.callCC (fun k => do
    k.1 42
    return 100)
  : FreeCont Nat Nat) id = 42 := by simp


example : FreeCont.run (do
  let x ← FreeCont.callCC (fun k => do
    if true then k.1 42 else return 100)
  return x + 1
  : FreeCont Nat Nat) id = 43 := by simp
