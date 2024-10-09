import Mathlib.Data.Finset.Basic
import Mathlib.Data.Greedoid.Basic
import Mathlib.Order.Minimal

namespace Greedoid

variable {α : Type*}

def Bases (G : Greedoid α) : Finset α → Prop := fun s ↦
  Maximal (fun t ↦ t ∈ G ∧ t ⊆ G.ground_set) s

def Basis (G : Greedoid α) (s : Finset α) : Finset α → Prop := fun b ↦
  s ⊆ G.ground_set ∧ Maximal (fun t ↦ t ∈ G ∧ t ⊆ s) b

def Basis' (G : Greedoid α) (s : Finset α) : Finset α → Prop := fun b ↦
  Maximal (fun t ↦ t ∈ G ∧ t ⊆ s) b

section Basis

variable {G : Greedoid α} {s b : Finset α}

theorem bases_eq_basis'_ground : G.Bases = G.Basis' G.ground_set := by
  funext x; simp only [Bases, Basis']

theorem bases_eq_basis_ground : G.Bases = G.Basis G.ground_set := by
  funext x; simp [Bases, Basis]

theorem bases_feasible (hb : G.Bases b) : b ∈ G :=
  hb.prop.1

theorem basis'_feasible (hb : G.Basis s b) : b ∈ G :=
  hb.2.prop.1

theorem basis_feasible (hb : G.Basis s b) : b ∈ G :=
  hb.2.prop.1

theorem bases_subset_ground (hb : G.Bases b) : b ⊆ G.ground_set :=
  hb.prop.2

theorem basis'_subset_ground (hb : G.Basis' s b) : b ⊆ G.ground_set :=
  hb.2.prop.1

end Basis

end Greedoid

