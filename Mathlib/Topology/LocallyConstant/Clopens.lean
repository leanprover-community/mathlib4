import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sets.Closeds

/--
The set of clopen subsets of a topological space is equivalent to the locally constant maps to
a two-element set
-/
def LocallyConstant.equivClopens (X : Type*) [TopologicalSpace X]
    [∀ (s : Set X) x, Decidable (x ∈ s)] :
    LocallyConstant X (Fin 2) ≃ TopologicalSpace.Clopens X where
  invFun s := ofIsClopen s.2
  toFun f := ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp
