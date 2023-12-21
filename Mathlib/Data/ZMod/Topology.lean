import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Constructions

namespace ZMod
/-- Making `ZMod` a discrete topological space. -/
instance {d : ℕ} : TopologicalSpace (ZMod d) := ⊥

instance {d : ℕ} : DiscreteTopology (ZMod d) := { eq_bot := rfl }
end ZMod

@[continuity]
lemma induced_top_cont_inv {n : ℕ} : @Continuous _ _ (TopologicalSpace.induced
    (Units.coeHom (ZMod n)) inferInstance) _ (Units.inv : (ZMod n)ˣ → ZMod n) :=
by
  convert continuous_of_discreteTopology
  refine' DiscreteTopology_induced (λ a b h => Units.eq_iff.1 h)
