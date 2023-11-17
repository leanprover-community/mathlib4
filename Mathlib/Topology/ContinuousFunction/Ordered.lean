/-
Copyright © 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam
-/
import Mathlib.Topology.Algebra.Order.ProjIcc
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.continuous_function.ordered from "leanprover-community/mathlib"@"84dc0bd6619acaea625086d6f53cb35cdd554219"

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/


variable {α : Type*} {β : Type*} {γ : Type*}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace ContinuousMap

section

variable [LinearOrderedAddCommGroup β] [OrderTopology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) where toFun x := |f x|
#align continuous_map.abs ContinuousMap.abs

-- see Note [lower instance priority]
instance (priority := 100) : Abs C(α, β) :=
  ⟨fun f => abs f⟩

@[simp]
theorem abs_apply (f : C(α, β)) (x : α) : |f| x = |f x| :=
  rfl
#align continuous_map.abs_apply ContinuousMap.abs_apply

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/


section Lattice

instance partialOrder [PartialOrder β] : PartialOrder C(α, β) :=
  PartialOrder.lift (fun f => f.toFun) (fun f g _ => by cases f; cases g; congr)
  -- porting note: was `by tidy`, and `by aesop` alone didn't work
#align continuous_map.partial_order ContinuousMap.partialOrder

theorem le_def [PartialOrder β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def
#align continuous_map.le_def ContinuousMap.le_def

theorem lt_def [PartialOrder β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def
#align continuous_map.lt_def ContinuousMap.lt_def

instance sup [LinearOrder β] [OrderClosedTopology β] : Sup C(α, β) where
  sup f g := { toFun := fun a => max (f a) (g a) }
#align continuous_map.has_sup ContinuousMap.sup

@[simp, norm_cast]
theorem sup_coe [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊔ g : C(α, β)) : α → β) = (f ⊔ g : α → β) :=
  rfl
#align continuous_map.sup_coe ContinuousMap.sup_coe

@[simp]
theorem sup_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊔ g) a = max (f a) (g a) :=
  rfl
#align continuous_map.sup_apply ContinuousMap.sup_apply

instance semilatticeSup [LinearOrder β] [OrderClosedTopology β] : SemilatticeSup C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.sup with
    le_sup_left := fun f g => le_def.mpr (by simp [le_refl])
    le_sup_right := fun f g => le_def.mpr (by simp [le_refl])
    sup_le := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance inf [LinearOrder β] [OrderClosedTopology β] : Inf C(α, β) where
  inf f g := { toFun := fun a => min (f a) (g a) }
#align continuous_map.has_inf ContinuousMap.inf

@[simp, norm_cast]
theorem inf_coe [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) :
    ((f ⊓ g : C(α, β)) : α → β) = (f ⊓ g : α → β) :=
  rfl
#align continuous_map.inf_coe ContinuousMap.inf_coe

@[simp]
theorem inf_apply [LinearOrder β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) :
    (f ⊓ g) a = min (f a) (g a) :=
  rfl
#align continuous_map.inf_apply ContinuousMap.inf_apply

instance semilatticeInf [LinearOrder β] [OrderClosedTopology β] : SemilatticeInf C(α, β) :=
  { ContinuousMap.partialOrder,
    ContinuousMap.inf with
    inf_le_left := fun f g => le_def.mpr (by simp [le_refl])
    inf_le_right := fun f g => le_def.mpr (by simp [le_refl])
    le_inf := fun f₁ f₂ g w₁ w₂ => le_def.mpr fun a => by simp [le_def.mp w₁ a, le_def.mp w₂ a] }

instance [LinearOrder β] [OrderClosedTopology β] : Lattice C(α, β) :=
  { ContinuousMap.semilatticeInf, ContinuousMap.semilatticeSup with }

-- TODO transfer this lattice structure to `BoundedContinuousFunction`
section Sup'

variable [LinearOrder γ] [OrderClosedTopology γ]

theorem sup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  Finset.comp_sup'_eq_sup'_comp H (fun f : C(β, γ) => f b) fun _ _ => rfl
#align continuous_map.sup'_apply ContinuousMap.sup'_apply

@[simp, norm_cast]
theorem sup'_coe {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.sup' H f : C(β, γ)) : β → γ) = s.sup' H fun a => (f a : β → γ) := by
  ext
  simp [sup'_apply]
#align continuous_map.sup'_coe ContinuousMap.sup'_coe

end Sup'

section Inf'

variable [LinearOrder γ] [OrderClosedTopology γ]

theorem inf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @sup'_apply _ γᵒᵈ _ _ _ _ _ _ H f b
#align continuous_map.inf'_apply ContinuousMap.inf'_apply

@[simp, norm_cast]
theorem inf'_coe {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.inf' H f : C(β, γ)) : β → γ) = s.inf' H fun a => (f a : β → γ) :=
  @sup'_coe _ γᵒᵈ _ _ _ _ _ _ H f
#align continuous_map.inf'_coe ContinuousMap.inf'_coe

end Inf'

end Lattice

section Extend

variable [LinearOrder α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(Set.Icc a b, β)` to a function `f : C(α, β)`.  -/
def IccExtend (f : C(Set.Icc a b, β)) : C(α, β) where
  toFun := Set.IccExtend h f
#align continuous_map.Icc_extend ContinuousMap.IccExtend

@[simp]
theorem coe_IccExtend (f : C(Set.Icc a b, β)) :
    ((IccExtend h f : C(α, β)) : α → β) = Set.IccExtend h f :=
  rfl
#align continuous_map.coe_Icc_extend ContinuousMap.coe_IccExtend

end Extend

end ContinuousMap
