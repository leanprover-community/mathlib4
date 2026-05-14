import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring 
import Mathlib.Data.Fin.Basic

namespace vizing

variable {V : Type*} (G : SimpleGraph V) (α : Type*)

/-- The edge coloring of a graph is the vertex coloring of its line graph. -/
def edgeColoring := G.lineGraph.Coloring α

/-- A graph is edge colorable with `n` colors if its line graph is `n`-colorable. -/
def edgeColorable (n : ℕ) : Prop := G.lineGraph.Colorable n

/-- The chromatic index of `G` is the chromatic number of its line graph. -/
noncomputable def chromaticIndex [Fintype V] : ℕ :=
  G.lineGraph.chromaticNumber.toNat

end vizing
