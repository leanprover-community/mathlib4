/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Krause
-/
import Mathlib.Order.CompleteSublattice

variable (α : Type*) [Order.Frame α]

variable (S : CompleteSublattice α)

def minAx2 : Order.Frame.MinimalAxioms α where
  inf_sSup_le_iSup_inf := Order.Frame.inf_sSup_le_iSup_inf

def minAx : Order.Frame.MinimalAxioms S :=
  Subtype.coe_injective.frameMinimalAxioms ⟨Order.Frame.inf_sSup_le_iSup_inf⟩ _ (fun _ _ ↦ rfl)
  (fun _ _ ↦ rfl) CompleteSublattice.coe_sSup' CompleteSublattice.coe_sInf' (rfl) (rfl)

instance instFrame : Order.Frame S :=
  Order.Frame.ofMinimalAxioms (minAx α S)
