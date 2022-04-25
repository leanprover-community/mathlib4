import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.ToAdditive

open Lean

attribute [to_additive Add] Mul
attribute [to_additive Zero] One
attribute [to_additive Zero.toOfNat0] One.toOfNat1
attribute [to_additive Zero.ofOfNat0] One.ofOfNat1
attribute [to_additive Neg] Inv
attribute [to_additive Sub] Div

attribute [to_additive HAdd] HMul
attribute [to_additive instHAdd]  instHMul
attribute [to_additive HSub] HDiv
