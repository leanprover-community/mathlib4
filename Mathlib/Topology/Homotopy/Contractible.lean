/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala

! This file was ported from Lean 3 source module topology.homotopy.contractible
! leanprover-community/mathlib commit 16728b3064a1751103e1dc2815ed8d00560e0d87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homotopy.Path
import Mathbin.Topology.Homotopy.Equiv

/-!
# Contractible spaces

In this file, we define `contractible_space`, a space that is homotopy equivalent to `unit`.
-/


noncomputable section

namespace ContinuousMap

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A map is nullhomotopic if it is homotopic to a constant map. -/
def Nullhomotopic (f : C(X, Y)) : Prop :=
  ∃ y : Y, Homotopic f (ContinuousMap.const _ y)
#align continuous_map.nullhomotopic ContinuousMap.Nullhomotopic

theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by rfl⟩
#align continuous_map.nullhomotopic_of_constant ContinuousMap.nullhomotopic_of_constant

theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) :
    (g.comp f).Nullhomotopic := by
  cases' hf with y hy
  use g y
  exact homotopic.hcomp hy (homotopic.refl g)
#align continuous_map.nullhomotopic.comp_right ContinuousMap.Nullhomotopic.comp_right

theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by
  cases' hf with y hy
  use y
  exact homotopic.hcomp (homotopic.refl g) hy
#align continuous_map.nullhomotopic.comp_left ContinuousMap.Nullhomotopic.comp_left

end ContinuousMap

open ContinuousMap

open ContinuousMap

/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`hequiv_unit] [] -/
/-- A contractible space is one that is homotopy equivalent to `unit`. -/
class ContractibleSpace (X : Type _) [TopologicalSpace X] : Prop where
  hequiv_unit : Nonempty (X ≃ₕ Unit)
#align contractible_space ContractibleSpace

theorem id_nullhomotopic (X : Type _) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic :=
  by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.inv_fun ()
  convert hv.left_inv.symm
  ext; simp; congr
#align id_nullhomotopic id_nullhomotopic

theorem contractible_iff_id_nullhomotopic (Y : Type _) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic :=
  by
  constructor;
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine_struct
    {
      hequiv_unit :=
        ⟨{  toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p }⟩ }
  · exact h.symm;
  · convert homotopic.refl (ContinuousMap.id Unit)
    ext
#align contractible_iff_id_nullhomotopic contractible_iff_id_nullhomotopic

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩
#align continuous_map.homotopy_equiv.contractible_space ContinuousMap.HomotopyEquiv.contractibleSpace

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨by
    intro h
    exact e.symm.contractible_space, by
    intro h
    exact e.contractible_space⟩
#align continuous_map.homotopy_equiv.contractible_space_iff ContinuousMap.HomotopyEquiv.contractibleSpace_iff

protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.ContractibleSpace
#align homeomorph.contractible_space Homeomorph.contractibleSpace

protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff
#align homeomorph.contractible_space_iff Homeomorph.contractibleSpace_iff

namespace ContractibleSpace

instance (priority := 100) [ContractibleSpace X] : PathConnectedSpace X :=
  by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : ∀ x, Joined p x := fun x => ⟨(h.eval_at x).symm⟩
  rw [pathConnectedSpace_iff_eq]; use p; ext; tauto

end ContractibleSpace

