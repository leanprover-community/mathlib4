import Mathlib.RingTheory.RingHom.FiniteType
import Lean

open Lean Elab Tactic Term

syntax "algebraize" (ppSpace colGt term:max)* : tactic

elab_rules : tactic
  | `(tactic| algebraize $[$t:term]*) => do
    for f in t do
      let elabedF ← Term.elabTerm f none
      let .app (.app (.app (.app (.const ``RingHom _) _) _) _) _ ← Meta.inferType elabedF |
        throwError "Type of {elabedF} is not a ring hom"
      evalTactic <| ← `(tactic|letI := (RingHom.toAlgebra $f))

example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  algebraize f g
  trivial
