import Mathlib.Topology.Category.Profinite.AsLimit

open CategoryTheory Limits FintypeCat


noncomputable
def Light : (ℕ ⥤ FintypeCat) ⥤ Profinite := (whiskeringRight _ _ _).obj toProfinite ⋙ lim
