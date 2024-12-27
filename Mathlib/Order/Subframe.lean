import Mathlib.Order.CompleteSublattice
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic


variable (α : Type*) [Order.Frame α]

abbrev Subframe := @CompleteSublattice α _


variable (S : Subframe α)

def minAx2 : Order.Frame.MinimalAxioms α where
  inf_sSup_le_iSup_inf := Order.Frame.inf_sSup_le_iSup_inf

def minAx : Order.Frame.MinimalAxioms S :=
  Subtype.coe_injective.frameMinimalAxioms (minAx2 α) _ (fun _ _ ↦ rfl)
  (fun _ _ ↦ rfl) CompleteSublattice.coe_sSup'
  CompleteSublattice.coe_sInf' (rfl) (rfl)


instance instFrame : Order.Frame S :=
  Order.Frame.ofMinimalAxioms (minAx α S)
