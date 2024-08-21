import Mathlib.RingTheory.Perfection

/-!
# Perfectoid Rings and Perfectoid Fields
-/

open Valuation Valued

class PerfectoidField (K : Type u) {Γ : outParam Type*} [Field K] [LinearOrderedCommGroup Γ] [vK : Valued K Γ] [vK.v.RankOne] : Prop where
  complete : IsComplete K
  
