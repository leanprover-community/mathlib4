import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails

variable {V : Type} {G : SimpleGraph V} {u v : V}

def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop := sorry

-- See
#check SimpleGraph.Walk.IsEulerian

def SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) : Prop := sorry

def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop := sorry

def Dirac {G : SimpleGraph V} (degree_condition : sorry) : G.IsHamiltonian := sorry
