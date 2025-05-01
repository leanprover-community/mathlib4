import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

open Filter

variable {α : Type*} {f : Filter α} {u v : α → EReal} (h : u ≤ᶠ[f] v)
-- proof term
example : limsup u f ≤ limsup v f := limsup_le_limsup h

-- exact
example : limsup u f ≤ limsup v f := by exact limsup_le_limsup h

-- apply
example : limsup u f ≤ limsup v f := by apply limsup_le_limsup h
