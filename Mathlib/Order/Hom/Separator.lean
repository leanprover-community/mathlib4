import Mathlib.Order.Hom.Bounded
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Zorn

universe u
variable {α : Type} [Lattice α] [BoundedOrder α] [DistribLattice α]

variable (F : InfTopHom α Prop) (G : SupBotHom α Prop)

def separator : BoundedLatticeHom α Prop := by sorry

theorem separator_contains_filter : setOf F.1 ⊆ setOf separator := by sorry

theorem separator_disjoint_from_ideal  : setOf separator ∩ setOf G.1 = ∅ := by sorry
