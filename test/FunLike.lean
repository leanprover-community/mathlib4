import Mathlib.Data.FunLike.Basic

variable {F α β : Sort*} [i : FunLike F α fun _ ↦ β] (f : F) (a : α)

/-- info: f a : β -/
#guard_msgs in #check f a
