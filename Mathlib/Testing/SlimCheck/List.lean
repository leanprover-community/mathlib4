import Mathlib.Data.List.Basic
import Mathlib.Testing.SlimCheck.Sampleable
import Mathlib.Tactic

open SlimCheck Shrinkable SampleableExt

/-- Shrink a list of a shrinkable type, either by discarding an element or shrinking an element. -/
instance List.shrinkable [Shrinkable α] : Shrinkable (List α) where
  shrink := fun L =>
    (L.mapIdx fun i _ => L.removeNth i) ++
    (L.mapIdx fun i a => (shrink a).map fun a' => L.modifyNth (fun _ => a') i).join

instance List.sampleableExt [SampleableExt α] [Repr α] [Shrinkable α] : SampleableExt (List α) where
  proxy := List (proxy α)
  sample := Gen.listOf sample
  interp := List.map interp

-- #sample List Int
-- Prints something like:
-- []
-- []
-- []
-- [2]
-- [3, -1, 1, 2]
-- [-4, 3, 2]
-- []
-- [6, -7]
-- [-1]
-- [-9]
