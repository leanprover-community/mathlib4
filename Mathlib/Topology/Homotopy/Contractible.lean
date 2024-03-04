/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Equiv

#align_import topology.homotopy.contractible from "leanprover-community/mathlib"@"16728b3064a1751103e1dc2815ed8d00560e0d87"

/-!
# Contractible spaces

In this file, we define `ContractibleSpace`, a space that is homotopy equivalent to `Unit`.
-/

noncomputable section

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

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
  exact Homotopic.hcomp hy (Homotopic.refl g)
#align continuous_map.nullhomotopic.comp_right ContinuousMap.Nullhomotopic.comp_right

theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by
  cases' hf with y hy
  use y
  exact Homotopic.hcomp (Homotopic.refl g) hy
#align continuous_map.nullhomotopic.comp_left ContinuousMap.Nullhomotopic.comp_left

end ContinuousMap

open ContinuousMap

/-- A contractible space is one that is homotopy equivalent to `Unit`. -/
class ContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  hequiv_unit' : Nonempty (X ≃ₕ Unit)
#align contractible_space ContractibleSpace

-- Porting note: added to work around lack of infer kinds
theorem ContractibleSpace.hequiv_unit (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    Nonempty (X ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit'
#align contractible_space.hequiv_unit ContractibleSpace.hequiv_unit

theorem id_nullhomotopic (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert hv.left_inv.symm
#align id_nullhomotopic id_nullhomotopic

theorem contractible_iff_id_nullhomotopic (Y : Type*) [TopologicalSpace Y] :
    ContractibleSpace Y ↔ (ContinuousMap.id Y).Nullhomotopic := by
  constructor
  · intro
    apply id_nullhomotopic
  rintro ⟨p, h⟩
  refine
    { hequiv_unit' :=
        ⟨{  toFun := ContinuousMap.const _ ()
            invFun := ContinuousMap.const _ p
            left_inv := ?_
            right_inv := ?_ }⟩ }
  · exact h.symm
  · convert Homotopic.refl (ContinuousMap.id Unit)
#align contractible_iff_id_nullhomotopic contractible_iff_id_nullhomotopic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩
#align continuous_map.homotopy_equiv.contractible_space ContinuousMap.HomotopyEquiv.contractibleSpace

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩
#align continuous_map.homotopy_equiv.contractible_space_iff ContinuousMap.HomotopyEquiv.contractibleSpace_iff

protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.contractibleSpace
#align homeomorph.contractible_space Homeomorph.contractibleSpace

protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff
#align homeomorph.contractible_space_iff Homeomorph.contractibleSpace_iff

namespace ContractibleSpace

instance [Unique Y] : ContractibleSpace Y := by
  have : ContractibleSpace (Unit) := ⟨⟨HomotopyEquiv.refl Unit⟩⟩
  apply (Homeomorph.homeomorphOfUnique Y Unit).contractibleSpace

variable (X Y) in
theorem hequiv [ContractibleSpace X] [ContractibleSpace Y] :
    Nonempty (X ≃ₕ Y) := by
  rcases ContractibleSpace.hequiv_unit' (X := X) with ⟨h⟩
  rcases ContractibleSpace.hequiv_unit' (X := Y) with ⟨h'⟩
  exact ⟨h.trans h'.symm⟩

instance (priority := 100) [ContractibleSpace X] : PathConnectedSpace X := by
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X
  have : ∀ x, Joined p x := fun x => ⟨(h.evalAt x).symm⟩
  rw [pathConnectedSpace_iff_eq]; use p; ext; tauto

end ContractibleSpace
