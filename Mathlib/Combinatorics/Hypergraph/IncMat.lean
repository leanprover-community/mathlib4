import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Defs
import Mathlib.Combinatorics.Hypergraph.Basic

open Set Finset Hypergraph

-- TODO: need to prove that IsIncident is decidable
-- See `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`

variable {α β : Type*} {x y z : α} {s t : Set α} {e f g : β} {l m : Set β}
variable (H : Hypergraph α β) [DecidableRel H.IsIncident]

/-! ## Incidence Matrix -/

def incidenceMatrix (H : Hypergraph α β) : Matrix α β Bool :=
  fun x e => if H.IsIncident x e then true else false
