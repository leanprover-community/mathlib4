import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

variable {V W : Type*} {v w : V} {G : SimpleGraph V} {G' : SimpleGraph W}
variable (f : G ≃g G') [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet (f v))]

instance : Fintype (G'.neighborSet (f v)) :=
  Fintype.ofEquiv ↑(G.neighborSet v) (f.mapNeighborSet v)

theorem apply_mem_neighborFinset_iff : f w ∈ G'.neighborFinset (f v) ↔ w ∈ G.neighborFinset v :=
  Iff.trans (G'.mem_neighborFinset (f v) (f w)) (Iff.trans (f.map_adj_iff (v := v) (w:= w))
   (G.mem_neighborFinset v w).symm)

def mapNeighborFinset (v : V) [Fintype (G.neighborSet v)] [Fintype (G'.neighborSet (f v))] :
    G.neighborFinset v ≃ G'.neighborFinset (f v) where
  toFun w := ⟨f w, (apply_mem_neighborFinset_iff f).mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using (apply_mem_neighborFinset_iff f.symm).mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

theorem degree_map_eq : G'.degree (f v) = G.degree v :=
  eq_comm.1 (Finset.card_eq_of_equiv (mapNeighborFinset f v))
