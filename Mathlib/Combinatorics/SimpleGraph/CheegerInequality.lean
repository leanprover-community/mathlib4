import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Function.Indicator


open BigOperators Finset Matrix

variable {V : Type*} (α : Type*)
variable [Fintype V] [Nonempty V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Field α] [AddGroupWithOne α] -- Field makes spectrum_finset work

def volume (s : Finset V) : ℕ := ∑ v in s, G.degree v

def edge_boundary (s : Set V) : Set (V × V) := {(u, v) | (u ∈ s) ∧ v ∉ s ∧ G.Adj u v}

-- Where to provide the proof that this is a set of edges?
def edge_boundary_v2 (s : Set V) : Set (SimpleGraph.edgeSet G) := Sym2.mk '' (edge_boundary G s)

def cut (s : Finset V) : ℕ := ∑ u in s, ∑ v in sᶜ, (if G.Adj u v then 1 else 0)

noncomputable def conductance (s : Finset V) : α := cut G s / min (volume G s) (volume G sᶜ)

-- Will need the set which attains the minimum
noncomputable def min_conductance : ℝ := (Finset.powerset (Finset.univ : Finset V)).inf'
  (by apply Finset.powerset_nonempty) (conductance ℝ G)

noncomputable def eigenvalues_finset : Finset (Module.End.Eigenvalues (Matrix.toLin' (G.lapMatrix α)))
  := Finset.univ

-- how to make this work for α?
noncomputable def pos_eigenvalues :=
  Set.toFinset {x : Module.End.Eigenvalues (Matrix.toLin' (G.lapMatrix ℝ)) | x > (0 : ℝ)}

-- how to get rid of this?
--variable [LinearOrder (Module.End.Eigenvalues (toLin' (SimpleGraph.lapMatrix ℝ G)))]

--noncomputable def eigenvalues_list := Finset.sort (LE.le) (eigenvalues_finset ℝ G)

theorem eigenvalues_list_length : 1 < (eigenvalues_list G).length := by
  sorry



noncomputable def spectral_gap := (pos_eigenvalues G).min' sorry


/-
noncomputable def my_vector (s : Finset V): V → ℝ := Set.indicator s 1

lemma asdf (s : Finset V) : R(my_vector G s) = 2 * (min_conductance G) := sorry
-/

theorem cheeger_ineq_easy : spectral_gap G ≤ 2 * (min_conductance G) := sorry

theorem cheeger_ineq_hard : min_conductance G^2 / 2 ≤ spectral_gap G := sorry
