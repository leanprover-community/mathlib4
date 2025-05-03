import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Category.Ring.Topology

namespace CommRingCat.HomTopology
open TensorProduct CategoryTheory
universe u
variable {T : CommRingCat.{u}}
variable {R S : Under T}

scoped instance [TopologicalSpace S] : TopologicalSpace (R ⟶ S) :=
  .induced (fun f ↦ f.right) inferInstance

end CommRingCat.HomTopology
