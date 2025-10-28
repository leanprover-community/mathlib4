/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Equiv

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

theorem nullhomotopic_of_constant (y : Y) : Nullhomotopic (ContinuousMap.const X y) :=
  ⟨y, by rfl⟩

theorem Nullhomotopic.comp_right {f : C(X, Y)} (hf : f.Nullhomotopic) (g : C(Y, Z)) :
    (g.comp f).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use g y
  exact .comp (.refl g) hy

theorem Nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.Nullhomotopic) (g : C(X, Y)) :
    (f.comp g).Nullhomotopic := by
  obtain ⟨y, hy⟩ := hf
  use y
  exact .comp hy (.refl g)

end ContinuousMap

open ContinuousMap

/-- A contractible space is one that is homotopy equivalent to `Unit`. -/
class ContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  hequiv_unit' : Nonempty (X ≃ₕ Unit)

theorem ContractibleSpace.hequiv_unit (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    Nonempty (X ≃ₕ Unit) :=
  ContractibleSpace.hequiv_unit'

theorem id_nullhomotopic (X : Type*) [TopologicalSpace X] [ContractibleSpace X] :
    (ContinuousMap.id X).Nullhomotopic := by
  obtain ⟨hv⟩ := ContractibleSpace.hequiv_unit X
  use hv.invFun ()
  convert hv.left_inv.symm

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

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace [ContractibleSpace Y] (e : X ≃ₕ Y) :
    ContractibleSpace X :=
  ⟨(ContractibleSpace.hequiv_unit Y).map e.trans⟩

protected theorem ContinuousMap.HomotopyEquiv.contractibleSpace_iff (e : X ≃ₕ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  ⟨fun _ => e.symm.contractibleSpace, fun _ => e.contractibleSpace⟩

protected theorem Homeomorph.contractibleSpace [ContractibleSpace Y] (e : X ≃ₜ Y) :
    ContractibleSpace X :=
  e.toHomotopyEquiv.contractibleSpace

protected theorem Homeomorph.contractibleSpace_iff (e : X ≃ₜ Y) :
    ContractibleSpace X ↔ ContractibleSpace Y :=
  e.toHomotopyEquiv.contractibleSpace_iff

namespace ContractibleSpace

instance [Nonempty Y] [Subsingleton Y] : ContractibleSpace Y :=
  let ⟨_⟩ := nonempty_unique Y
  ⟨⟨(Homeomorph.homeomorphOfUnique Y Unit).toHomotopyEquiv⟩⟩

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
