import Mathlib.Tactic.LabelAttr
import Lean.Util.Trace

open Lean

register_label_attr functor

initialize registerTraceClass `Tactic.transport
