import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option linter.style.setOption false
set_option pp.unicode.fun true
set_option linter.style.commandStart false

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {s : Set V} {x : V}

variable (h : LinearIndependent K (fun b => b : s → V)) in
/-- info: h : LinearIndependent K fun (b : ↑s) ↦ ↑b -/
#guard_msgs in #check h

variable (h : LinearIndependent K (Subtype.val : s → V)) in
/-- info: h : LinearIndependent K Subtype.val -/
#guard_msgs in #check h

variable (h : LinearIndependent K (by exact Subtype.val : s → V)) in
/-- info: h : LinearIndependent (ι := ↑s) K Subtype.val -/
#guard_msgs in #check h

variable (h : LinearIndependent K (fun b => (fun b => b : s → V) b)) in
/-- info: h : LinearIndependent K fun (b : ↑s) ↦ (fun b ↦ ↑b) b -/
#guard_msgs in #check h
